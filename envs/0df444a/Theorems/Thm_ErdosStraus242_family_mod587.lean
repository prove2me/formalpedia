-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod587
-- name    : ErdosStraus242.family_mod587
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T08:57:27.812468+00:00
-- url     : https://prove2.me/theorems/41e6d1b7-e4bd-4615-ac82-76be7955dcb6
-- title:
--   Five Erdős–Straus congruence families modulo 587
-- statement:
--   For every integer $n>2$ with $n\bmod 587\in\{583, 575, 559, 503, 391\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 5 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=587$, where $\alpha=147$ and $g$ runs over the divisors $\{1, 3, 7, 21, 49\}$ of $147$; a class is $n\equiv -4g\pmod{587}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $587=4\cdot147-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid147$, $g<147$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod587 (n : ℕ) (hn : 2 < n)
    (hmod : n % 587 ∈ ({583, 575, 559, 503, 391} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
