-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod463
-- name    : ErdosStraus242.family_mod463
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T08:56:24.907193+00:00
-- url     : https://prove2.me/theorems/40247dad-65b1-4726-99fc-dec20e7d9e5d
-- title:
--   Five Erdős–Straus congruence families modulo 463
-- statement:
--   For every integer $n>2$ with $n\bmod 463\in\{459, 455, 447, 347, 231\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 5 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=463$, where $\alpha=116$ and $g$ runs over the divisors $\{1, 2, 4, 29, 58\}$ of $116$; a class is $n\equiv -4g\pmod{463}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $463=4\cdot116-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid116$, $g<116$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod463 (n : ℕ) (hn : 2 < n)
    (hmod : n % 463 ∈ ({459, 455, 447, 347, 231} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
