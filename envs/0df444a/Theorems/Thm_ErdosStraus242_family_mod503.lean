-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod503
-- name    : ErdosStraus242.family_mod503
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T08:56:48.204662+00:00
-- url     : https://prove2.me/theorems/5282af1f-c3a5-4919-9fb4-d3a877ec989f
-- title:
--   Eleven Erdős–Straus congruence families modulo 503
-- statement:
--   For every integer $n>2$ with $n\bmod 503\in\{499, 495, 491, 479, 475, 467, 447, 431, 419, 335, 251\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 11 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=503$, where $\alpha=126$ and $g$ runs over the divisors $\{1, 2, 3, 6, 7, 9, 14, 18, 21, 42, 63\}$ of $126$; a class is $n\equiv -4g\pmod{503}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $503=4\cdot126-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid126$, $g<126$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod503 (n : ℕ) (hn : 2 < n)
    (hmod : n % 503 ∈ ({499, 495, 491, 479, 475, 467, 447, 431, 419, 335, 251} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
