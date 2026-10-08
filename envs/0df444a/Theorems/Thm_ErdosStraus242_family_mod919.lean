-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod919
-- name    : ErdosStraus242.family_mod919
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:52:06.539427+00:00
-- url     : https://prove2.me/theorems/c3d9d75e-a32b-4a5a-b1f0-ddd89221c81d
-- title:
--   Seven Erdős–Straus congruence families modulo 919
-- statement:
--   For every integer $n>2$ with $n\bmod 919\in\{915, 911, 899, 879, 827, 735, 459\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 7 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=919$, where $\alpha=230$ and $g$ runs over the divisors $\{1, 2, 5, 10, 23, 46, 115\}$ of $230$; a class is $n\equiv -4g\pmod{919}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $919=4\cdot230-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid230$, $g<230$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod919 (n : ℕ) (hn : 2 < n)
    (hmod : n % 919 ∈ ({915, 911, 899, 879, 827, 735, 459} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
