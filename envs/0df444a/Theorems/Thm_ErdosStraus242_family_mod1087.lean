-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod1087
-- name    : ErdosStraus242.family_mod1087
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T23:41:57.749967+00:00
-- url     : https://prove2.me/theorems/d01edf69-5e7f-4378-8a9c-bb190f15c66a
-- title:
--   Nine Erdős–Straus congruence families modulo 1087
-- statement:
--   For every integer $n>2$ with $n\bmod 1087\in\{1083, 1079, 1071, 1055, 1023, 1019, 951, 815, 543\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 9 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=1087$, where $\alpha=272$ and $g$ runs over the divisors $\{1, 2, 4, 8, 16, 17, 34, 68, 136\}$ of $272$; a class is $n\equiv -4g\pmod{1087}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $1087=4\cdot272-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid272$, $g<272$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod1087 (n : ℕ) (hn : 2 < n)
    (hmod : n % 1087 ∈ ({1083, 1079, 1071, 1055, 1023, 1019, 951, 815, 543} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
