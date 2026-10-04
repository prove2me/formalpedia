-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod799
-- name    : ErdosStraus242.family_mod799
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:32:32.504378+00:00
-- url     : https://prove2.me/theorems/03ebabe6-116a-4f98-b5e2-7c69af40fe48
-- title:
--   Eleven Erdős–Straus congruence families modulo 799
-- statement:
--   For every integer $n>2$ with $n\bmod 799\in\{795, 791, 783, 779, 767, 759, 719, 699, 639, 599, 399\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 11 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=799$, where $\alpha=200$ and $g$ runs over the divisors $\{1, 2, 4, 5, 8, 10, 20, 25, 40, 50, 100\}$ of $200$; a class is $n\equiv -4g\pmod{799}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $799=4\cdot200-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid200$, $g<200$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod799 (n : ℕ) (hn : 2 < n)
    (hmod : n % 799 ∈ ({795, 791, 783, 779, 767, 759, 719, 699, 639, 599, 399} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
