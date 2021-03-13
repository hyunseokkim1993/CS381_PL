#ifndef PL4_H
#define PL4_H

#include <string>
#include <iostream>
#include <set>
#include <map>
#include <algorithm>

class Literal
{
public:
	////////////////////////////////////////////////////////////////////////
	// Functions
	////////////////////////////////////////////////////////////////////////
	Literal(std::string const& _name) : name(_name), negated(false) { }
	Literal() : name(""), negated(false) { } // just for map.operator[]

	Literal& Negate()
	{
		negated = !negated;
		return *this;
	}
	bool IsPositive() const { return !negated; }
	bool Complementary(Literal const& op2) const
	{
		return (name == op2.name) && (negated != op2.negated);
	}
	std::string GetName() const;
	
	////////////////////////////////////////////////////////////////////////
	// Operator
	////////////////////////////////////////////////////////////////////////
	bool operator==(Literal const& op2) const
	{
		Literal const& op1 = *this;
		return (op1.negated == op2.negated) && (op1.name == op2.name);
	}
	bool operator<(Literal const& op2) const
	{
		Literal const& op1 = *this;
		if (op1.negated && !op2.negated) 
		{
			return true;
		}
		if (!op1.negated && op2.negated) 
		{
			return false;
		}
		return (op1.name < op2.name);
	}
	Literal operator~() const
	{
		Literal result(*this);
		result.Negate();
		return result;
	}
	Literal operator=(Literal rhs) const
	{
		Literal result(*this);
		result.name = rhs.name;
		result.negated = rhs.negated;
		return result;
	}
	friend std::ostream& operator<<(std::ostream& os, Literal const& literal) {
		os << (literal.negated ? "~" : "") << literal.name;
		return os;
	}
private:
	std::string name;
	bool negated;
};

class Clause {
public:
	////////////////////////////////////////////////////////////////////////
	// Functions
	////////////////////////////////////////////////////////////////////////
	Clause() {}
	Clause(Literal const& op2)
	{
		literals.insert(op2);
	}
	void Insert(const Literal& litr);
	bool IsEmpty();
	bool DoesExist(const Literal litr);
	unsigned Size() const;
	std::set< Literal >::const_iterator begin() const;
	std::set< Literal >::const_iterator end() const;
	std::set< Literal >::reverse_iterator crend() const;
	std::set< Literal >::reverse_iterator crbegin() const;

	////////////////////////////////////////////////////////////////////////
	// Operator
	////////////////////////////////////////////////////////////////////////
	bool operator<(const Clause& op2) const
	{
		if (Size() == op2.Size())
		{
			auto iter1 = literals.begin();
			auto iter2 = op2.literals.begin();
			auto end1 = literals.end();
			auto end2 = op2.literals.end();

			for(		; iter1 != end1 && iter2 != end2; ++iter1, ++iter2)
			{
				if (iter1 == literals.end() || iter2 == op2.literals.end())
				{
					return false;
				}
				if (*iter1 == *iter2)
				{
					continue;
				}
				return (*iter1) < (*iter2);
			}
		}
		else
		{
			return Size() < op2.Size();
		}
		return false;
	}
	////////////////////////////////////////////////////////////////////////
	friend std::ostream& operator<<(std::ostream& os, Clause const& clause)
	{
		unsigned size = static_cast<unsigned>(clause.literals.size());
		if(size == 0){
			os << " FALSE ";
		}
		else {
			std::set<Literal>::const_iterator it = clause.literals.begin();
			os << "( " << *it;
			++it;
			for (; it != clause.literals.end(); ++it) {
				os << " | " << *it;
			}
			os << " ) ";
		}
		return os;
	}
	bool operator==(const Clause& rhs) const
	{
		if (Size() != rhs.Size())
		{
			return false;
		}

		auto iter1 = literals.begin();
		auto iter2 = rhs.literals.begin();
		auto end1 = literals.end();
		auto end2 = rhs.literals.end();
		
		for (		; iter1 != end1 && iter2 != end2; ++iter1, ++iter2)
		{
			if (((*iter1).GetName() == (*iter2).GetName()) && ((*iter1).IsPositive() == (*iter2).IsPositive()))
			{
				continue;
			}
			return false;
		}
		return true;
	}
private:
	std::set<Literal> literals;
};

class CNF {
public:
	// ..........
	// ..........
	// ..........
	// ..........
	CNF() {};
	CNF(Literal const& op2)
	{
		Clause cl(op2);
		clauses.insert(cl);
	};
	CNF(Clause const& op2)
	{
		clauses.insert(op2);
	}
	CNF(std::set<Clause> const& op2)
	{
		clauses.insert(op2.begin(), op2.end());
	}
	////////////////////////////////////////////////////////////////////////
	// not
	CNF const operator~() const
	{
		//if CNF is made of a single clause: A | B | ~C,
		//negating it gives ~A & ~B & C (3 clauses)
		//otherwise
		//CNF = clause1 & clause2 & clause3,
		//~CNF = ~clause1 | ~clause2 | ~clause3 
		//"or" is defined later 
		CNF result;
		std::set<Clause> temp;
		if (clauses.size() == 1)
		{
			auto iter = clauses.begin();
			auto end = clauses.end();
			
			for (		; iter != end; ++iter)
			{
				std::set<Literal> l_result;

				auto iter2 = (*iter).begin();
				auto end2 = (*iter).end();
				
				for (		; iter2 != end2; ++iter2)
				{
					Literal lit = (*iter2);
					lit.Negate();
					Clause cl_result(lit);
					temp.emplace(cl_result);
				}
			}
			result.clauses = temp;
			return result;
		}

		auto iter = clauses.begin();
		auto end = clauses.end();
		
		CNF result2(*(iter));
		for (		; iter != clauses.end(); ++iter)
		{
			if (iter == clauses.begin())
			{
				continue;
			}
			result2 = ~result2 | ~CNF(*iter);
		}
		return result2;
	}
	////////////////////////////////////////////////////////////////////////
	// =>
	CNF const operator>(CNF const& op2) const
	{
		CNF const& op1 = *this;
		return ~(op1) | op2;
	}
	////////////////////////////////////////////////////////////////////////
	// and
	CNF const operator&(CNF const& op2) const
	{
		//CNF1 = clause1 & clause2 & clause3,
		//CNF2 = clause4 & clause5 & clause6,
		//CNF1 & CNF2 = clause1 & clause2 & clause3 & clause4 & clause5 & clause6
		CNF result;

		if (clauses.empty() || op2.clauses.empty())
		{
			return result;
		}
		result.clauses.insert(clauses.begin(), clauses.end());
		result.clauses.insert(op2.clauses.begin(), op2.clauses.end());
		return result;
	}
	///////////////////////////////////////////////////////////////////////
	// or
	CNF const operator|(CNF const& op2) const
	{
		//CNF1 = clause1 & clause2 & clause3,
		//CNF2 = clause4 & clause5 & clause6,
		//CNF1 | CNF2 = 
		//              c1|c4 & c1|c5 & c1|c6    &
		//              c2|c4 & c2|c5 & c2|c6    &
		//              c3|c4 & c3|c5 & c3|c6
		
		if (clauses.empty())
		{
			std::set<Clause> cla;
			cla.insert(op2.begin(), op2.end());
			CNF result(cla);
			return result;
		}
		if (op2.clauses.empty())
		{
			std::set<Clause> cla;
			cla.insert(clauses.begin(), clauses.end());
			CNF result(cla);
			return result;
		}

		auto iter1 = clauses.begin();
		auto iter2 = op2.begin();
		auto end1 = clauses.end();
		auto end2 = op2.end();

		CNF result;
		
		for (		; iter1 != end1; ++iter1)
		{
			for (		; iter2 != end2; ++iter2)
			{
				auto iter3 = (*iter1).begin();
				auto iter4 = (*iter2).begin();
				auto end3 = (*iter1).end();
				auto end4 = (*iter2).end();

				Clause cla;

				for (		; iter3 != end3; ++iter3)
				{
					cla.Insert(*iter3);
				}
				for (		; iter4 != end4; ++iter4)
				{
					cla.Insert(*iter4);
				}
				result.clauses.insert(cla);
			}
		}
		
		return result;
	}

	/////////////////////////////////////////////////////////////////////////////////
	CNF const operator>(Literal const& op2) const { return operator>(CNF(op2)); }
	CNF const operator&(Literal const& op2) const { return operator&(CNF(op2)); }
	CNF const operator|(Literal const& op2) const { return operator|(CNF(op2)); }
	////////////////////////////////////////////////////////////////////////
	bool Empty() const { return clauses.size() == 0; }
	////////////////////////////////////////////////////////////////////////
	std::set< Clause >::const_iterator begin() const { return clauses.begin(); }
	std::set< Clause >::const_iterator end()   const { return clauses.end(); }
	unsigned                           size()  const { return static_cast<unsigned>(clauses.size()); }
	////////////////////////////////////////////////////////////////////////
	friend std::ostream& operator<<(std::ostream& os, CNF const& cnf) {
		//unsigned Size = cnf.clauses.Size();
		for (std::set<Clause>::const_iterator it1 = cnf.clauses.begin(); it1 != cnf.clauses.end(); ++it1) {
			os << *it1 << ", ";
		}
		return os;
	}
private:
	std::set<Clause> clauses;
};

CNF const operator|(Literal const& op1, Literal const& op2);
CNF const operator|(Literal const& op1, CNF     const& op2);
CNF const operator&(Literal const& op1, Literal const& op2);
CNF const operator&(Literal const& op1, CNF     const& op2);
CNF const operator>(Literal const& op1, Literal const& op2);
CNF const operator>(Literal const& op1, CNF     const& op2);

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
class KnowledgeBase {
public:
	////////////////////////////////////////////////////////////////////////////
	KnowledgeBase();
	////////////////////////////////////////////////////////////////////////////
	KnowledgeBase& operator+=(CNF const& cnf);
	////////////////////////////////////////////////////////////////////////
	std::set< Clause >::const_iterator begin() const;
	std::set< Clause >::const_iterator end()   const;
	unsigned                           size()  const;
	////////////////////////////////////////////////////////////////////////////
	bool ProveByRefutation(CNF const& alpha) const;
	std::set<Clause> Erase	(Clause const& c1, Clause const& c2) const;
	std::set<Clause> Resolve(Clause const& c1, Clause const& c2) const;
	////////////////////////////////////////////////////////////////////////////
	friend std::ostream& operator<<(std::ostream& os, KnowledgeBase const& kb);
private:
	std::set< Clause > clauses;
};

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
#endif
