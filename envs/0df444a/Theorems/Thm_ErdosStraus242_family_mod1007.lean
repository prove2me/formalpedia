-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod1007
-- name    : ErdosStraus242.family_mod1007
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T23:41:39.047878+00:00
-- url     : https://prove2.me/theorems/4b0ca61e-46ec-4614-bca6-0aba76b42585
-- title:
--   Seventeen Erdős–Straus congruence families modulo 1007
-- statement:
--   For every integer $n>2$ with $n\bmod 1007\in\{1003, 999, 995, 991, 983, 979, 971, 959, 951, 935, 923, 895, 863, 839, 755, 671, 503\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 17 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=1007$, where $\alpha=252$ and $g$ runs over the divisors $\{1, 2, 3, 4, 6, 7, 9, 12, 14, 18, 21, 28, 36, 42, 63, 84, 126\}$ of $252$; a class is $n\equiv -4g\pmod{1007}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $1007=4\cdot252-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid252$, $g<252$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod1007 (n : ℕ) (hn : 2 < n)
    (hmod : n % 1007 ∈ ({1003, 999, 995, 991, 983, 979, 971, 959, 951, 935, 923, 895, 863, 839, 755, 671, 503} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
