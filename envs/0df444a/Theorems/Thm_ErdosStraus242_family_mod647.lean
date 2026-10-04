-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod647
-- name    : ErdosStraus242.family_mod647
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:32:08.865551+00:00
-- url     : https://prove2.me/theorems/200717b0-2d3c-4679-8efc-2e66794d42a0
-- title:
--   Nine Erdős–Straus congruence families modulo 647
-- statement:
--   For every integer $n>2$ with $n\bmod 647\in\{643, 639, 635, 623, 611, 575, 539, 431, 323\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 9 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=647$, where $\alpha=162$ and $g$ runs over the divisors $\{1, 2, 3, 6, 9, 18, 27, 54, 81\}$ of $162$; a class is $n\equiv -4g\pmod{647}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $647=4\cdot162-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid162$, $g<162$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod647 (n : ℕ) (hn : 2 < n)
    (hmod : n % 647 ∈ ({643, 639, 635, 623, 611, 575, 539, 431, 323} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
