-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod883
-- name    : ErdosStraus242.family_mod883
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:51:58.121917+00:00
-- url     : https://prove2.me/theorems/101ab88e-5d79-4277-8805-6b652bf43938
-- title:
--   Three Erdős–Straus congruence families modulo 883
-- statement:
--   For every integer $n>2$ with $n\bmod 883\in\{879, 831, 815\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 3 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=883$, where $\alpha=221$ and $g$ runs over the divisors $\{1, 13, 17\}$ of $221$; a class is $n\equiv -4g\pmod{883}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $883=4\cdot221-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid221$, $g<221$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod883 (n : ℕ) (hn : 2 < n)
    (hmod : n % 883 ∈ ({879, 831, 815} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
