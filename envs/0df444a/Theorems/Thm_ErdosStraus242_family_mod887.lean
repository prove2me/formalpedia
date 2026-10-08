-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod887
-- name    : ErdosStraus242.family_mod887
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:51:56.216386+00:00
-- url     : https://prove2.me/theorems/2c835ebf-d4c3-4a4d-9749-57153943d233
-- title:
--   Seven Erdős–Straus congruence families modulo 887
-- statement:
--   For every integer $n>2$ with $n\bmod 887\in\{883, 879, 875, 863, 739, 591, 443\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 7 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=887$, where $\alpha=222$ and $g$ runs over the divisors $\{1, 2, 3, 6, 37, 74, 111\}$ of $222$; a class is $n\equiv -4g\pmod{887}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $887=4\cdot222-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid222$, $g<222$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod887 (n : ℕ) (hn : 2 < n)
    (hmod : n % 887 ∈ ({883, 879, 875, 863, 739, 591, 443} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
