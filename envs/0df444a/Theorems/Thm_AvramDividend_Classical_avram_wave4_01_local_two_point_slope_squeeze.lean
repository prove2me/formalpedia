-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_local_two_point_slope_squeeze
-- name    : AvramDividend.Classical.avram_wave4_01_local_two_point_slope_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:19:40.254992+00:00
-- url     : https://prove2.me/theorems/31a4a739-b186-402f-814c-7af39c861e78
-- title:
--   Continuous local two-point slope envelope implies differentiability
-- statement:
--   If a real-valued function has its two-point slope trapped between min and max of a continuous coefficient κ whenever the second argument is sufficiently near the positive first argument, then the function is differentiable there with derivative κ. The local restriction |b-a|<a/2 is designed for the authentic first-record sandwich, which requires upward height strictly smaller than the drawdown barrier.
-- source:
--   Local derivative squeeze adapted from accepted continuous two-point slope argument; resolves h<a domain of genuine first-record q-scale sandwich for cd61d678.

import Mathlib

open Filter Topology Set
open scoped Topology

theorem AvramDividend.Classical.avram_wave4_01_local_two_point_slope_squeeze
    (f κ : ℝ → ℝ)
    (hκ : ContinuousOn κ (Ioi (0 : ℝ)))
    (hslope : ∀ a b : ℝ, 0 < a → 0 < b → a ≠ b →
      |b - a| < a / 2 →
      min (κ a) (κ b) ≤ slope f a b ∧
        slope f a b ≤ max (κ a) (κ b)) :
    ∀ a : ℝ, 0 < a → HasDerivAt f (κ a) a := by sorry
