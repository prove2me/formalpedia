-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod1079
-- name    : ErdosStraus242.family_mod1079
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T23:41:53.313275+00:00
-- url     : https://prove2.me/theorems/5e36f787-7b30-4795-a0ed-88c4f1aed0e1
-- title:
--   Fifteen Erdős–Straus congruence families modulo 1079
-- statement:
--   For every integer $n>2$ with $n\bmod 1079\in\{1075, 1071, 1067, 1059, 1055, 1043, 1039, 1019, 1007, 971, 959, 899, 863, 719, 539\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 15 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=1079$, where $\alpha=270$ and $g$ runs over the divisors $\{1, 2, 3, 5, 6, 9, 10, 15, 18, 27, 30, 45, 54, 90, 135\}$ of $270$; a class is $n\equiv -4g\pmod{1079}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $1079=4\cdot270-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid270$, $g<270$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod1079 (n : ℕ) (hn : 2 < n)
    (hmod : n % 1079 ∈ ({1075, 1071, 1067, 1059, 1055, 1043, 1039, 1019, 1007, 971, 959, 899, 863, 719, 539} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
