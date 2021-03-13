#include "pl.h"

CNF const operator|(Literal const& op1, Literal const& op2) { return CNF(op1) | CNF(op2); }
CNF const operator|(Literal const& op1, CNF     const& op2) { return CNF(op1) | op2; }
CNF const operator&(Literal const& op1, Literal const& op2) { return CNF(op1) & CNF(op2); }
CNF const operator&(Literal const& op1, CNF     const& op2) { return CNF(op1) & op2; }
CNF const operator>(Literal const& op1, Literal const& op2) { return CNF(op1) > CNF(op2); }
CNF const operator>(Literal const& op1, CNF     const& op2) { return CNF(op1) > op2; }

std::string Literal::GetName() const
{
	return name;
}

void Clause::Insert(const Literal& litr)
{
	literals.emplace(litr);
}
std::set< Literal >::const_iterator Clause::begin() const
{
	return literals.begin();
}
std::set< Literal >::const_iterator Clause::end() const
{
	return literals.end();
}
std::set< Literal >::reverse_iterator Clause::crend() const
{
	return literals.crend();
}
std::set< Literal >::reverse_iterator Clause::crbegin() const
{
	return literals.crbegin();
}
unsigned Clause::Size() const
{
	return static_cast<unsigned>(literals.size());
}
bool Clause::IsEmpty()
{
	return literals.empty();
}
bool Clause::DoesExist(const Literal litr)
{
	for (auto data : literals)
	{
		if (litr == data)
			return true;
	}
	return false;
}

KnowledgeBase::KnowledgeBase() : clauses() {}
////////////////////////////////////////////////////////////////////////////
KnowledgeBase& KnowledgeBase::operator+=(CNF const& cnf) {
	for (std::set< Clause >::const_iterator it = cnf.begin(); it != cnf.end(); ++it) {
		clauses.insert(*it);
	}
	return *this;
}
////////////////////////////////////////////////////////////////////////
std::set< Clause >::const_iterator KnowledgeBase::begin() const { return clauses.begin(); }
std::set< Clause >::const_iterator KnowledgeBase::end()   const { return clauses.end(); }
unsigned                           KnowledgeBase::size()  const { return static_cast<unsigned>(clauses.size()); }

////////////////////////////////////////////////////////////////////////////
bool KnowledgeBase::ProveByRefutation(CNF const& alpha) const
{
	if (clauses.empty())
	{
		return true;
	}

	std::set<Clause> simplified;

	auto b = clauses.begin();
	auto e = clauses.end();

	for (		; b != e; ++b)
	{
		auto b2 = b;

		for (; b2 != e; ++b2)
		{
			Clause a = *b;
			Clause b = *b2;

			if (a == b)
			{
				continue;
			}

			std::set<Clause> temp = Erase(a, b);

			auto b3 = temp.begin();
			auto e3 = temp.end();

			for (; b3 != e3; ++b3)
			{
				simplified.insert(*b3);
			}
		}
	}

	if (simplified.empty())
	{
		return false;
	}
	
	CNF lhs(clauses);
	lhs = lhs & ~alpha;
	std::set<Clause> set;
	set.insert(lhs.begin(), lhs.end());
	std::set<Clause> result;
	while (true)
	{
		auto iter1 = set.begin();
		auto end = set.end();
		
		for (		; iter1 != end; ++iter1)
		{
			auto iter2 = iter1;
			
			for (		; iter2 != end; ++iter2)
			{
				Clause a = *iter1;
				Clause b = *iter2;
				
				if (a == b)
				{
					continue;
				}
				
				std::set<Clause> cla = Resolve(a, b);

				if (cla.empty())
				{
					return true;
				}
				result.insert(cla.begin(), cla.end());
			}
		}
		bool isSame = true;

		auto iter3 = result.begin();
		auto end3 = result.end();
		
		for (		; iter3 != end3; ++iter3) // new
		{
			if(set.find(*iter3) == end)
			{
				isSame = false;
				break;
			}
		}
		if (isSame)
		{
			return false;
		}

		set.insert(result.begin(), result.end());
	}
	return false;
}
////////////////////////////////////////////////////////////////////////////
std::ostream& operator<<(std::ostream& os, KnowledgeBase const& kb) {
	for (std::set< Clause >::const_iterator it1 = kb.clauses.begin(); it1 != kb.clauses.end(); ++it1) {
		os << *it1 << ", ";
	}
	return os;
}

std::set<Clause> KnowledgeBase::Erase(Clause const& c1, Clause const& c2) const
{
	std::set<Literal> literals;

	auto iter = c1.begin();
	auto end = c1.end();

	for (; iter != end; ++iter)
	{
		literals.emplace(*iter);
	}

	iter = c2.begin();
	end = c2.end();

	for (; iter != end; ++iter)
	{
		literals.emplace(*iter);
	}

	std::set<Literal> temp = literals;
	std::set<Clause> result;

	iter = temp.begin();
	end = temp.end();

	for (; iter != end; ++iter)
	{
		Literal lit = (*iter);
		Literal complt = ~lit;
		if (std::find(literals.begin(), literals.end(), complt) != literals.end())
		{
			literals.erase(lit);
			literals.erase(complt);
		}
	}

	Clause set_literal;

	iter = literals.begin();
	end = literals.end();

	for	(		; iter != end; ++iter)
	{
		set_literal.Insert(*iter);
	}
	if (!set_literal.IsEmpty())
	{
		result.emplace(set_literal);
	}
	return result;
}


std::set<Clause> KnowledgeBase::Resolve(Clause const& c1, Clause const& c2) const
{
	std::set<Literal> compLiteral;
	compLiteral.insert(c1.begin(), c1.end());
	std::set<Clause> remainder;

	bool isModified = false;

	auto iter = c2.begin();
	auto end = c2.end();

	for (; iter != end; ++iter)
	{
		Literal complt = ~(*iter);
		if (compLiteral.find(complt) != compLiteral.end())
		{
			isModified = true;
			compLiteral.erase(complt);
		}
		else
		{
			compLiteral.insert(*iter);
		}
	}
	if (isModified == false)
	{
		remainder.insert(c1);
		remainder.insert(c2);
	}
	else
	{
		if (compLiteral.empty())
		{
			std::set<Clause> empty;
			return empty;
		}

		Clause cla;

		auto iter2 = compLiteral.begin();
		auto end2 = compLiteral.end();
		for (; iter2 != end2; ++iter2)
		{
			cla.Insert(*iter2);
		}
		remainder.emplace(cla);
	}
	return remainder;
}