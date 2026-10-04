-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod527
-- name    : ErdosStraus242.family_mod527
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T08:56:59.542994+00:00
-- url     : https://prove2.me/theorems/10c73671-16ad-4c4f-a57d-bc25556e5e4d
-- title:
--   Eleven Erdős–Straus congruence families modulo 527
-- statement:
--   For every integer $n>2$ with $n\bmod 527\in\{523, 519, 515, 511, 503, 483, 479, 439, 395, 351, 263\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 11 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=527$, where $\alpha=132$ and $g$ runs over the divisors $\{1, 2, 3, 4, 6, 11, 12, 22, 33, 44, 66\}$ of $132$; a class is $n\equiv -4g\pmod{527}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $527=4\cdot132-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid132$, $g<132$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod527 (n : ℕ) (hn : 2 < n)
    (hmod : n % 527 ∈ ({523, 519, 515, 511, 503, 483, 479, 439, 395, 351, 263} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
