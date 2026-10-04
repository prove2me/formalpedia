-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod767
-- name    : ErdosStraus242.family_mod767
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:32:27.825102+00:00
-- url     : https://prove2.me/theorems/e710538e-a6db-4f23-adc3-a2392c6c4ac1
-- title:
--   Thirteen Erdős–Straus congruence families modulo 767
-- statement:
--   For every integer $n>2$ with $n\bmod 767\in\{763, 759, 755, 751, 743, 735, 719, 703, 671, 639, 575, 511, 383\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 13 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=767$, where $\alpha=192$ and $g$ runs over the divisors $\{1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96\}$ of $192$; a class is $n\equiv -4g\pmod{767}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $767=4\cdot192-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid192$, $g<192$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod767 (n : ℕ) (hn : 2 < n)
    (hmod : n % 767 ∈ ({763, 759, 755, 751, 743, 735, 719, 703, 671, 639, 575, 511, 383} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
