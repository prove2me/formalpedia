-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod671
-- name    : ErdosStraus242.family_mod671
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:32:14.978212+00:00
-- url     : https://prove2.me/theorems/99bc915b-14d3-4d61-bb78-5be863e8a328
-- title:
--   Fifteen Erdős–Straus congruence families modulo 671
-- statement:
--   For every integer $n>2$ with $n\bmod 671\in\{667, 663, 659, 655, 647, 643, 639, 623, 615, 587, 575, 559, 503, 447, 335\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 15 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=671$, where $\alpha=168$ and $g$ runs over the divisors $\{1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84\}$ of $168$; a class is $n\equiv -4g\pmod{671}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $671=4\cdot168-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid168$, $g<168$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod671 (n : ℕ) (hn : 2 < n)
    (hmod : n % 671 ∈ ({667, 663, 659, 655, 647, 643, 639, 623, 615, 587, 575, 559, 503, 447, 335} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
