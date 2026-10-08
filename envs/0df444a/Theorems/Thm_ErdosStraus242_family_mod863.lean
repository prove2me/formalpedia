-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod863
-- name    : ErdosStraus242.family_mod863
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:51:50.35785+00:00
-- url     : https://prove2.me/theorems/60440a2f-803e-47b6-88ce-1d34466e5ea2
-- title:
--   Fifteen Erdős–Straus congruence families modulo 863
-- statement:
--   For every integer $n>2$ with $n\bmod 863\in\{859, 855, 851, 847, 839, 831, 827, 815, 791, 767, 755, 719, 647, 575, 431\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 15 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=863$, where $\alpha=216$ and $g$ runs over the divisors $\{1, 2, 3, 4, 6, 8, 9, 12, 18, 24, 27, 36, 54, 72, 108\}$ of $216$; a class is $n\equiv -4g\pmod{863}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $863=4\cdot216-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid216$, $g<216$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod863 (n : ℕ) (hn : 2 < n)
    (hmod : n % 863 ∈ ({859, 855, 851, 847, 839, 831, 827, 815, 791, 767, 755, 719, 647, 575, 431} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
