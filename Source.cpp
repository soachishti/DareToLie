#include <iostream>
#include <vector>
#include <string>
#include <regex>
#include <map>
#include <tuple>

#include <algorithm> 
#include <functional> 
#include <cctype>
#include <locale>


#define CONJUNCTION		1
#define NEGATION		2
#define IMPLICATION		3
#define BI_IMPLICATION	4
#define NORMAL			5
#define DISJUNCTION		6
#define NOTHING			7

using namespace std;

typedef pair<bool, char>			pInfo;
typedef tuple<pInfo, int, pInfo>	premiseInfo;

class DareToLie_Owais {
protected:
	char ch = 'a';
	map <char, string> propositions;
	vector<premiseInfo> premises;
	vector<string> negWord;
public:
	DareToLie_Owais() {
		negWord.push_back("not");
		negWord.push_back("don't");
		negWord.push_back("dont");
	}

	pInfo addProposition(string p) {
		char tmp = ch;

		if (ch == 'z') ch = 'A';
		if (ch == 'Z')  {
			cout << "No more variables.";
			return make_pair(0,ch);
		}

		// if proposition already exists
		for (auto it = propositions.rbegin(); it != propositions.rend(); ++it) {
			if (isNegation(p) && it->second == removeNegation(p))
			{
				return make_pair(1, it->first);
			}
			if (it->second == p) {
				return make_pair(0, it->first);
			}
		}

		ch++;

		// Add if proposition in negated
		if (isNegation(p)) {
			propositions[tmp] = removeNegation(p);
			return make_pair(1, tmp);

		}
		else {
			propositions[tmp] = removeNegation(p);
			return make_pair(0,tmp);
		}
	}

	void printPropositions() {
		for (auto str : propositions) {
			cout << str.first << "\t" << str.second << endl;
		}
		cout << endl;
	}

	void printPremises() {
		for (auto str : premises) {
			int condition = get<1>(str);

			if (condition == NEGATION) {
				cout << "~"
					 << ((get<0>(str).first) ? "~" : "") << get<0>(str).second << endl;
			}
			else {
				cout << ((get<0>(str).first) ? "~" : "") << get<0>(str).second << "\t";
				switch (condition) {
				case BI_IMPLICATION:	cout << "<->";	break;
				case IMPLICATION:		cout << "->";	break;
				case CONJUNCTION:		cout << "^";	break;
				case DISJUNCTION:		cout << "v";	break;
				}
				cout << "\t" 
					 << ((get<2>(str).first) ? "~" : "") 
					 << get<2>(str).second << endl;

			}	
		}
		cout << endl;
	}

	premiseInfo addPremises(pInfo id, int relation, pInfo id2 = make_pair(0, 0)) {
		premises.push_back(
			make_tuple(
				id,
				relation,
				id2
			)
		);
		return make_tuple(
			id,
			relation,
			id2
			);
	}

	bool isNegation(string str) {
		for (string s : negWord) {
			size_t found = str.find(s);
			if (found != string::npos) 
				return true;
		}
		return false;
	}

	string removeNegation(string str) {
		for (string s : negWord) {
			size_t found = str.find(s);
			if (found != string::npos)
				str.erase(found, s.size() + 1); // +1 for removing space
		}
		return str;
	}

	void parseString(string str) {
		smatch m;
		regex e("\\s*([a-zA-Z0-9 ]+)\\.\\s*");
		
		while (regex_search(str, m, e)) {
			string str1 =  m[1];    // 
			smatch m1;
			regex e1("\\s*(.*)\\s+(then|and|or)\\s+(.*)");
			bool flag = false;
			while (regex_search(str1, m1, e1)) {
				flag = true;
				auto a = addProposition(m1[1]);
				auto b = addProposition(m1[3]);

				int condition;
				if (m1[2] == "then")      condition = IMPLICATION;
				else if (m1[2] == "and")  condition = CONJUNCTION;
				else if (m1[2] == "or")   condition = DISJUNCTION;
				addPremises(a, condition, b);

				str1 = m1.suffix().str();
			}

			// If sentence doesn't contain then, and, or.
			if (flag == false) {
				auto a = addProposition(str1);
				
				// If sentence is negate
				if (a.first == true) {
					a.first = 0;	// Remove double negation
					addPremises(a, NEGATION);
				}
				else {
					addPremises(a, NORMAL);
				}
			}
			str = m.suffix().str();
		}
	}
};

class DareToLie_Bilal : public DareToLie_Owais {
public:

	premiseInfo getRule(premiseInfo a, premiseInfo b) {
		// Rules of inference
		//	1) p
		//	   p -> q 
		if (get<0>(a).first == false && get<1>(a) == NORMAL &&			// p
			get<0>(a).second == get<0>(b).second &&
			get<0>(b).first == false &&									// p = p && not equal ~p
			get<1>(b) == IMPLICATION									// p -> q
			)
		{
			cout << "Rule 1\n";
			return make_tuple(get<2>(b), NORMAL, pInfo());
		}
		if (get<0>(b).first == false && get<1>(b) == NORMAL &&			// p
			get<0>(b).second == get<0>(a).second &&
			get<0>(a).first == false &&									// p = p && not equal ~p
			get<1>(a) == IMPLICATION									// p -> q
			)
		{
			cout << "Rule 1.1\n";
			return make_tuple(get<2>(a), NORMAL, pInfo());
		}
		else if (
			get<0>(a).first == false && get<1>(a) == NEGATION &&	// ~q
			get<0>(a).second == get<2>(b).second &&					// q = p -> q
			get<0>(b).first == false &&								// ~p X
			get<2>(b).first == false &&								// ~q
			get<1>(b) == IMPLICATION								// implication check
			)
		{
			cout << "Rule 2\n";
			get<0>(b).first = 0;
			return make_tuple(get<0>(b), NEGATION, pInfo());
		}
		else if (
			get<0>(b).first == false && get<1>(b) == NEGATION &&	// ~q
			get<0>(b).second == get<2>(a).second &&					// q = p -> q
			get<0>(a).first == false &&								// ~p X
			get<2>(a).first == false &&								// ~q
			get<1>(a) == IMPLICATION								// implication check
			)
		{
			cout << "Rule 2.1\n";
			get<0>(a).first = 0;
			return make_tuple(get<0>(a), NEGATION, pInfo());
		}
		else if (
			get<1>(a) == NORMAL &&
			get<1>(b) == NORMAL
			)
		{
			cout << "Rule 3\n";
			return make_tuple(get<0>(a), CONJUNCTION, get<0>(b));
		}
		//else if (
		//	get<1>(a) == NEGATION &&
		//	get<1>(b) == NEGATION
		//	)
		//{
		//	cout << "Rule 3.1\n";
		//	return make_tuple(get<0>(a), CONJUNCTION, get<0>(b));
		//}
		else if (
			get<2>(a).second == get<0>(b).second &&
			get<2>(a).second == get<0>(b).second &&
			get<2>(a).first == get<0>(b).first &&
			get<1>(a) == IMPLICATION &&
			get<1>(b) == IMPLICATION
			)
		{
			cout << "Rule 4\n";
			return make_tuple(get<0>(a), IMPLICATION, get<2>(b));
		}
		else if (
			get<2>(b).second == get<0>(a).second &&
			get<2>(b).second == get<0>(a).second &&
			get<2>(b).first == get<0>(a).first &&
			get<1>(b) == IMPLICATION &&
			get<1>(a) == IMPLICATION
			)
		{
			cout << "Rule 4.1n";
			return make_tuple(get<0>(b), IMPLICATION, get<2>(a));
		}

		else if (
			get<0>(a).second == get<0>(b).second &&
			get<0>(a).first == false &&
			get<1>(a) == NEGATION &&
			get<0>(b).first == false &&
			get<1>(b) == DISJUNCTION
			)
		{
			cout << "Rule 5\n";
			return make_tuple(get<2>(b), NORMAL, pInfo());
		}
		else if (
			get<0>(b).second == get<0>(a).second &&
			get<0>(a).first == false &&
			get<1>(a) == NORMAL &&
			get<0>(b).first == true &&
			get<1>(b) == DISJUNCTION
			)
		{
			cout << "Rule 5.1\n";
			return make_tuple(get<2>(b), NORMAL, pInfo());
		}
		else if (
			get<1>(b) == NEGATION &&
			get<1>(a) == DISJUNCTION &&
			get<0>(a).second == get<0>(b).second
			)
		{
			cout << "Rule 5.1.1\n";
			return make_tuple(get<2>(a), NORMAL, pInfo());
		}
		else if (
			get<1>(a) == NEGATION &&
			get<1>(b) == DISJUNCTION &&
			get<2>(b).first == false &&
			get<0>(a).second == get<2>(b).second
			)
		{
			cout << "Rule 5.2\n";
			get<0>(b).first = false;
			return make_tuple(get<0>(b), NEGATION, pInfo());
		}
		else if (
			get<1>(b) == NEGATION &&
			get<1>(a) == DISJUNCTION &&
			get<2>(a).first == false &&
			get<0>(b).second == get<2>(a).second
			)
		{
			cout << "Rule 5.3\n";
			get<0>(a).first = false;
			return make_tuple(get<0>(a), NORMAL, pInfo());
		}
		else if (
			get<2>(a).first == false &&
			get<0>(b).first == true &&
			get<1>(a) == DISJUNCTION &&
			get<1>(b) == DISJUNCTION &&
			get<2>(a).second == get<0>(b).second)
		{
			cout << "Rule 6\n";
			return make_tuple(get<0>(a), DISJUNCTION, get<2>(b));
		}
		else if (
			get<2>(a).first == true &&
			get<0>(b).first == false &&
			get<1>(a) == DISJUNCTION &&
			get<1>(b) == DISJUNCTION &&
			get<2>(a).second == get<0>(b).second)
		{
			cout << "Rule 6.1\n";
			return make_tuple(get<0>(a), DISJUNCTION, get<2>(b));
		}
		else if (
			get<1>(a) == NORMAL &&
			get<1>(b) == NORMAL &&
			get<0>(a).first == get<0>(b).first &&
			get<0>(a).second == get<0>(b).second
		)
		{
			cout << "Rule 7\n";
			return make_tuple(get<0>(a), NORMAL, pInfo());
		}
		else if (
			get<1>(a) == NEGATION &&
			get<1>(b) == NEGATION &&
			get<0>(a).first == get<0>(b).first &&
			get<0>(a).second == get<0>(b).second
			)
		{
			cout << "Rule 8\n";
			return make_tuple(get<0>(a), NEGATION, pInfo());
		}

		cout << "No match.\n";
		return make_tuple(
			make_pair(true, NULL),
			NOTHING, 
			make_pair(true, NULL)
			);
	}

	void solvePremises() {			
		int iter = 2;
		premiseInfo res;
		//while (premises.empty() == false) {
		while (iter--) {
			int count = 0;
			premiseInfo history;
			for (auto it = premises.begin(); it != premises.end(); /* ++it */) {
				if (count == 0) {
					history = *it;

					if (it != premises.end())
						it = premises.erase(it);
				}
				else {
					res = getRule(history, *it);
					printSinglePremise(history);
					printSinglePremise(*it);
					printSinglePremise(res);

					if (get<1>(res) == NOTHING) {
			 			cout << "Not applied." << endl;
						it++;
					}
					else {
						cout << "Applied Successfully." << endl;
						if (it != premises.end())
							it = premises.erase(it);

						cout << endl;
						history = res;
					}
				}
				count++;
			}
			if (get<1>(res) == NOTHING)
				premises.push_back(history);
			else 
				premises.push_back(res);
		}
		cout << "PRINTING RESULT:" << endl;

		for (auto p : premises) {
			printSinglePremise(res);
		}
	}

	void printSinglePremise(premiseInfo a) {
		if (get<1>(a) == NEGATION) cout << "~";

		if (get<0>(a).first == true) cout << "~";
		cout << get<0>(a).second << "\t";

		switch (get<1>(a)) {
		case BI_IMPLICATION:	cout << "<->";	break;
		case IMPLICATION:		cout << "->";	break;
		case CONJUNCTION:		cout << "^";	break;
		case DISJUNCTION:		cout << "v";	break;
		}
		cout << "\t";
		if (get<2>(a).first == true) cout << "~";
		cout << get<2>(a).second << endl;
	}
};

void main() {
	DareToLie_Bilal dtl;
	string str;
	
	/*
	// Test 004 Error
	str = "I put on table then I put in kitchen table. I dont put in kitchen table. I put in my room then I put on sidetable. I dont put in dining room. I put on sidetable then I put in dining room. I put on table or I put in my room. I put in dining room or I put in my room.";
	cout << str << endl << endl;
	dtl.parseString(str);
	dtl.printPropositions();
	dtl.printPremises();
	dtl.solvePremises();
	return;
	*/
	/*
	// Test 003 Successfull
	str = "I am Fakhar or I am Owais. I am not Fakhar. I am Bilal.";
	cout << str << endl << endl;
	dtl.parseString(str);
	dtl.printPropositions();
	dtl.printPremises();
	dtl.solvePremises();
	return;
	*/
	/*
	// Test 002 Successfull
	str = "I eat Apple then I eat banana. I eat banana then I drink Sting. I not drink Sting. I smoke cigarette or I eat banana. I not eat banana or I eat Apple.";
	cout << str << endl << endl;
	dtl.parseString(str);
	dtl.printPropositions();
	dtl.printPremises();
	dtl.solvePremises();
	return;
	*/
	
	// Test 001 Successfull
	str = "I live in Peshawar then I live in Pakistan. I live in Peshawar. I dont live in Pakistan or I live in London. I live in London then I live in England. I live in England then I live in Karachi.";
	cout << str << endl << endl;
	dtl.parseString(str);
	dtl.printPropositions();
	dtl.printPremises();
	dtl.solvePremises();
	
	return;	
} 