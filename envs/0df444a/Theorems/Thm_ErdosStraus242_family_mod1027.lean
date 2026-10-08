-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod1027
-- name    : ErdosStraus242.family_mod1027
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T23:41:42.219204+00:00
-- url     : https://prove2.me/theorems/689b6de5-9afd-45d7-b833-ceb597a5643a
-- title:
--   One Erdős–Straus congruence families modulo 1027
-- statement:
--   For every integer $n>2$ with $n\bmod 1027\in\{1023\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 1 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=1027$, where $\alpha=257$ and $g$ runs over the divisors $\{1\}$ of $257$; a class is $n\equiv -4g\pmod{1027}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $1027=4\cdot257-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid257$, $g<257$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod1027 (n : ℕ) (hn : 2 < n)
    (hmod : n % 1027 ∈ ({1023} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
