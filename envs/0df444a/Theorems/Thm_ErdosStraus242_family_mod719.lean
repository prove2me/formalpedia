-- Prove2me | Theorems.Thm_ErdosStraus242_family_mod719
-- name    : ErdosStraus242.family_mod719
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:32:20.260063+00:00
-- url     : https://prove2.me/theorems/4beff2ef-a916-4251-a30e-1af7d6970411
-- title:
--   Seventeen Erdős–Straus congruence families modulo 719
-- statement:
--   For every integer $n>2$ with $n\bmod 719\in\{715, 711, 707, 703, 699, 695, 683, 679, 671, 659, 647, 639, 599, 575, 539, 479, 359\}$ there are natural numbers $1\le x<y<z$ with $4/n=1/x+1/y+1/z$ in $\mathbb Q$. The 17 classes are the $(a,c,d)=(1,\alpha/g,g)$ specializations of the Bloom–Elsholtz parametrization at modulus $4\alpha-1=719$, where $\alpha=180$ and $g$ runs over the divisors $\{1, 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90\}$ of $180$; a class is $n\equiv -4g\pmod{719}$. The modulus is coprime to $840$ and was unsieved in the mission frontier; each class contains hard-core primes surviving all existing sieves. The statement keeps the mission's strict distinct-denominator convention.
-- source:
--   Bloom–Elsholtz, Theorem 1, pp. 239–240, https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf; cf. Erdős Problem 242, https://www.erdosproblems.com/242. Classes at modulus $719=4\cdot180-1$ from the triples $(a,c,d)=(1,\alpha/g,g)$, $g\mid180$, $g<180$.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem family_mod719 (n : ℕ) (hn : 2 < n)
    (hmod : n % 719 ∈ ({715, 711, 707, 703, 699, 695, 683, 679, 671, 659, 647, 639, 599, 575, 539, 479, 359} : Finset ℕ)) :
    IsErdosStraus n := by sorry
end ErdosStraus242
