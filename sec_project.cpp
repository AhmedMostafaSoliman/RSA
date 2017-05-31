#include <iostream>
#include <string>
#include <vector>
#include <queue> 
#include <algorithm>

#define FOR(i,n) for(int i=0; i<n ; i++)
#define all(x) (x).begin(), (x).end()

typedef long long ll;
typedef unsigned int uint;
typedef unsigned long long ull;
using namespace std;


vector<uint> as = { 2, 3, 5, 7}, two = { 2 }, one = { 1 }, zero = { 0 }, ten = { 10 };

inline bool isbigger(vector<uint> &v1, vector<uint> &v2)
{
	if (v1.size() != v2.size()) return v1.size() > v2.size();
	for (int i = v1.size() - 1; i >= 0; i--) if (v1[i] != v2[i]) return v1[i] > v2[i];
	return 0;
}

inline void add(vector<uint> &v1, vector<uint> &v2)
{
	ull cur = 0; int mn = min(v1.size(), v2.size()), mx = max(v1.size(), v2.size());
	FOR(i, mn)
	{
		cur += ull(v1[i]) + v2[i];
		v1[i] = cur & 0xffffffff; cur >>= 32;
	}
	if (v1.size() > v2.size()) for (int i = mn; i < mx; i++) cur += v1[i], v1[i] = cur & 0xffffffff, cur >>= 32;
	else for (int i = mn; i < mx; i++) cur += v2[i], v1.emplace_back(cur & 0xffffffff), cur >>= 32;
	if (cur) v1.emplace_back(cur);
}

inline void sub(vector<uint> &v1, vector<uint> &v2)
{
	ll cur = 0; bool nxt = 0;
	FOR(i, v2.size())
	{
		cur = ll(v1[i]) - v2[i] - nxt;
		if (cur < 0) cur += 0xffffffff + 1, nxt = 1; else nxt = 0;
		v1[i] = cur;
	}
	if (nxt) v1[v2.size()]--;
	while (v1.size() > 1 && v1[v1.size() - 1] == 0) v1.pop_back();
}

inline void srl(vector<uint> &v1)
{
	FOR(i, v1.size() - 1) { v1[i] >>= 1; v1[i] |= ((v1[i + 1] & 1) << 31); }
	v1[v1.size() - 1] >>= 1; while (v1.size() > 1 && !v1[v1.size() - 1]) v1.pop_back();
}

inline void srlby32(vector<uint> &v1)
{
	FOR(i, v1.size() - 1)v1[i] = v1[i + 1];
	if (v1.size()  >1)v1.pop_back();
}

inline void sll(vector<uint> &v1)
{
	int st = 0; if (v1[v1.size() - 1] & 0x80000000) v1.emplace_back(1), st = 1;
	for (int i = v1.size() - 1 - st; i > 0; i--){ v1[i] <<= 1; v1[i] |= bool(v1[i - 1] & 0x80000000); }
	v1[0] <<= 1;
}

inline void sllby32(vector<uint> &v1)
{
	uint dbg = v1[v1.size() - 1];
	v1.emplace_back(dbg);
	for (int i = v1.size() - 2; i > 0; i--){ v1[i] = v1[i - 1]; }
	v1[0] = 0;
}

inline void mul(vector<uint> &v1, vector<uint> &v2, vector<uint> &mulret)
{
	mulret.assign(v1.size() + v2.size(), 0);
	FOR(i, v2.size())
	{
		ull cur = 0;
		FOR(j, v1.size()){ cur += ull(v1[j]) * v2[i] + mulret[i + j]; mulret[i + j] = cur & 0xffffffff; cur >>= 32; }
		if (cur) mulret[i + v1.size()] += cur;
	}
	while (mulret.size() > 1 && !mulret[mulret.size() - 1]) mulret.pop_back();
}


inline void div(vector<uint> &v1, vector<uint> &v2, vector<uint> &mod, vector<uint> &res)
{
	res.assign(v1.size(), 0);  mod.assign(v2.size() - 1, 0); //mod.clear();
	if (v1 == v2) { mod = vector < uint > {0}; res = vector < uint > {1}; return; }
	else if (isbigger(v2, v1))  { mod = v1;  res = vector < uint > {0}; return; }
	int i = v1.size() - 1, j = 31, tmp1 = v1.size() - v2.size() + 1;
	if (v2.size() >1)for (; i >= tmp1; i--)	mod[i - tmp1] = v1[i]; else mod.emplace_back(0);
	while (i >= 0)
	{
		sll(mod);
		mod[0] |= bool(v1[i] & (1 << j));
		if (isbigger(mod, v2) || mod == v2)
		{
			sub(mod, v2);
			res[i] |= (1 << j);
		}
		if (j) j--;	else j = 31, i--;
	}
	while (res.size() > 1 && res[res.size() - 1] == 0) res.pop_back();
}

inline void Mod(vector<uint> &v1, vector<uint> &v2, vector<uint> &mod)
{
	mod.assign(v2.size() - 1, 0);
	if (v1 == v2) { mod = vector < uint > {0}; return; }
	else if (isbigger(v2, v1))  { mod = v1; return; }
	int i = v1.size() - 1, j = 31, tmp1 = v1.size() - v2.size() + 1;
	if (v2.size() >1)for (; i >= tmp1; i--)	mod[i - tmp1] = v1[i]; else mod.emplace_back(0);
	while (i >= 0)
	{
		sll(mod);
		mod[0] |= bool(v1[i] & (1 << j));
		if (isbigger(mod, v2) || mod == v2) sub(mod, v2);
		if (j) j--;	else j = 31, i--;
	}
}

inline vector<uint> modinv(vector<uint> &v, vector<uint> &mod)
{
	vector<uint> a3 = mod, b3 = v, t3, q, a2 = zero, t2, b2 = one, mulret;
	while (b3 != one)
	{
		div(a3, b3, t3, q);
		t2 = a2;
		mul(q, b2, mulret);
		while (isbigger(mulret, t2)) add(t2, mod);
		sub(t2, mulret);
		a2 = b2, a3 = b3; b2 = t2, b3 = t3;
	}
	return b2;
}


inline string big_to_string(vector<uint> v)
{
	string ret; ret.reserve(v.size() * 10);
	vector<uint> res, mod, subretdiv; subretdiv.resize(v.size() + 1); res.resize(v.size() + 1), mod.resize(v.size() + 1);
	while (isbigger(v, zero))
	{
		div(v, ten, mod, res);
		ret += mod[0] + '0';
		v = res;
	}
	reverse(all(ret));
	return ret;
}

inline vector<uint> string_to_big(string &s)
{
	vector<uint> ret = { 0 }, tmp2 = { 0 }, mulret; ret.reserve(1 + s.size() / 9); mulret.reserve(1 + s.size() / 9);
	if (s == "0") { ret.emplace_back(0); return ret; }
	FOR(i, s.length())
	{
		mul(ret, ten, mulret);  ret = mulret;
		tmp2[0] = { uint(s[i] - '0') };
		add(ret, tmp2);
	}
	return ret;
}

inline void pow(vector<uint> a, vector<uint> b, vector<uint> &m, vector<uint> &powret)
{
	vector<uint>  mod, mulret; mulret.reserve(2 * m.size() + 2); mod.reserve(2 * m.size() + 2);
	powret.clear(); powret.emplace_back(1);
	Mod(a, m, mod); a = mod;
	while (b != zero)
	{
		if (b[0] & 1)
		{
			mul(powret, a, mulret);
			Mod(mulret, m, powret);
		}
		mul(a, a, mulret);
		Mod(mulret, m, a);
		srl(b);
	}
}

inline bool isprime(vector<uint> &n)
{
	vector<uint> powret; powret.reserve(2 * n.size() + 1);
	if (n.size() == 1 && binary_search(all(as), n[0])) return 1;
	uint k = 0; vector<uint> a = { 2 };
	if (isbigger(two, n) || (!(n[0] & 1) && n != two)) return 0;
	vector<uint> nminus1 = n, q; sub(nminus1, one), q = nminus1;
	while (!(q[0] & 1))	k++, srl(q);
	bool ret = 1;
	FOR(i, as.size())
	{
		bool f = 0;
		a[0] = as[i];
		vector<uint> exp = q;
		pow(a, q, n, powret);
		if (powret == one || powret == nminus1){ret &= 1; continue;}
		for (int j = 1; j < k; j++)
		{
			sll(exp);
			pow(a, exp, n, powret);
			if (powret == nminus1) { f = 1; ret &= 1; break; }
		}
		if (!f) return 0;
	}
	return ret;
}

int main()
{	
	char tmp; string s;
	cin >> tmp >> tmp; cin >> s; vector<uint> p = string_to_big(s);
	cin >> tmp >> tmp; cin >> s; vector<uint> q = string_to_big(s);
	cin >> tmp >> tmp; cin >> s; vector<uint> e = string_to_big(s);
	vector<uint> n, phi, d;
	mul(p, q, n);sub(p, one); sub(q, one); mul(p, q, phi); add(p, one); add(q, one);d = modinv(e, phi);	
	while (cin>>s && s!="Quit")
	{
		if (s == "IsPPrime")
		{
			if (isprime(p)) cout << "Yes" << endl;	else cout << "No" << endl;
		}
		else if (s == "IsQPrime")
		{
			if (isprime(q)) cout << "Yes" << endl;	else cout << "No" << endl;
		}
		else if (s == "PrintN")		
			cout << big_to_string(n) << endl;
		
		else if (s == "PrintPhi")		
			cout << big_to_string(phi) << endl;
		
		else if (s == "PrintD")		
			cout << big_to_string(d) << endl;
		
		else
		{
			if (s[8] == 'u')
			{
				s = s.substr(15, s.length() - 16);
				vector<uint> m = string_to_big(s), c;
				pow(m, e, n, c);
				cout << big_to_string(c) << endl;
			}
			else
			{
				s = s.substr(16, s.length() - 17);
				vector<uint> c = string_to_big(s), m;
				pow(c, d, n, m);
				cout << big_to_string(m) << endl;
			}
		}
	}	
	return 0;	
}
