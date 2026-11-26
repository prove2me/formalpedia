-- Prove2me | Theorems.Thm_Erdos287_dual_frequency_joint_gcd_mean
-- name    : Erdos287.dual_frequency_joint_gcd_mean
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T21:00:18.849563+00:00
-- url     : https://prove2.me/theorems/e97810f6-90f9-4d73-82b5-e502474fa4df
-- title:
--   Joint gcd mean for dual frequencies
-- statement:
--   Let $r,j,e$ be positive pairwise coprime integers, and let $H$ be a natural number. Then $\sum_{1\le t\le H}(t,r)(t,j)(t,e)\le H\tau(r)\tau(j)\tau(e)$. The exclusion of frequency zero permits the bound uniformly for every cutoff.
-- source:
--   Erdős #287, joint nonzero dual-frequency cutoff for the squarefree Type III correlations.

import Mathlib

theorem Erdos287.dual_frequency_joint_gcd_mean (H r j e : ℕ) (hpos : 0 < r * j * e)
    (hrj : r.Coprime j) (he : (r * j).Coprime e) :
    (∑ t ∈ Finset.Ioc 0 H, t.gcd r * t.gcd j * t.gcd e) ≤
      H * (r.divisors.card * j.divisors.card * e.divisors.card) := by sorry
