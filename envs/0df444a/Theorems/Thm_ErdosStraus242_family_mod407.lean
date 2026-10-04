-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod407
-- name    : ErdosStraus242.family_mod407
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T07:38:08.825346+00:00
-- url     : https://prove2.me/theorems/cd4cf724-f757-40c8-a8d3-0c8bc04bf02b
-- title:
--   Seven Erdős–Straus congruence families modulo 407
-- statement:
--   For every integer $n>2$ with $n\bmod 407\in\{403, 399, 395, 383, 339, 271, 203\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The seven classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=407$, where $\alpha=102$ and $g$ runs over the divisors \{1,2,3,6,17,34,51\} of $102$; a class is $n\equiv -4g\pmod{407}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $407=4\cdot102-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$ with $g\in\{1,2,3,6,17,34,51\}$ the divisors of $102$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod407 (n : ℕ) (hn : 2 < n)
    (hmod : n % 407 ∈ ({403, 399, 395, 383, 339, 271, 203} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
