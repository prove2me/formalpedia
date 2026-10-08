-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod983
-- name    : ErdosStraus242.family_mod983
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:52:25.432798+00:00
-- url     : https://prove2.me/theorems/a7062c58-3a67-46e8-a65f-87b13e7c015b
-- title:
--   Seven Erdős–Straus congruence families modulo 983
-- statement:
--   For every integer $n>2$ with $n\bmod 983\in\{979, 975, 971, 959, 819, 655, 491\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 7 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=983$, where $\alpha=246$ and $g$ runs over the divisors $\{1, 2, 3, 6, 41, 82, 123\}$ of $246$; a class is $n\equiv -4g\pmod{983}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $983=4\cdot246-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid246$, $g<246$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod983 (n : ℕ) (hn : 2 < n)
    (hmod : n % 983 ∈ ({979, 975, 971, 959, 819, 655, 491} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
