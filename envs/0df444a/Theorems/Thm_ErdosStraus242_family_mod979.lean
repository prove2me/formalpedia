-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod979
-- name    : ErdosStraus242.family_mod979
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:52:17.376766+00:00
-- url     : https://prove2.me/theorems/9d2a2242-b0d0-41f8-82cf-eb2496bb6ece
-- title:
--   Five Erdős–Straus congruence families modulo 979
-- statement:
--   For every integer $n>2$ with $n\bmod 979\in\{975, 959, 951, 839, 783\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 5 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=979$, where $\alpha=245$ and $g$ runs over the divisors $\{1, 5, 7, 35, 49\}$ of $245$; a class is $n\equiv -4g\pmod{979}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $979=4\cdot245-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid245$, $g<245$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod979 (n : ℕ) (hn : 2 < n)
    (hmod : n % 979 ∈ ({975, 959, 951, 839, 783} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
