-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_continuous_two_point_slope_squeeze
-- name    : AvramDividend.Classical.avram_wave3_01_continuous_two_point_slope_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:47:47.29888+00:00
-- url     : https://prove2.me/theorems/ea9cce90-c3d1-4821-b02e-ef1a887a0134
-- title:
--   Continuous two-point slope envelopes yield the exact derivative on the positive axis
-- statement:
--   For real f and a continuous positive-axis envelope κ, if every two-point slope of f between distinct positive arguments lies between κ at its two endpoints, then f has ordinary derivative κ(a) at every a>0. The proof uses the exact pinned Mathlib slope characterisation of HasDerivAt and the eventual-order squeeze theorem. In the original Lévy source C1 proof, f=log W and κ is the Proved continuous record log hazard. This lemma isolates general analysis from the stochastic reciprocal-factor and scale-ratio bounds.
-- source:
--   Canonical Avram C1 root cd61d678; continuous log-rate provider ec9e934a and reciprocal log-sandwich algebra 966eda12. Mathlib hasDerivAt_iff_tendsto_slope and Filter.Tendsto.squeeze' pinned.

import Mathlib
open Filter Topology Set
open scoped Topology

theorem AvramDividend.Classical.avram_wave3_01_continuous_two_point_slope_squeeze
    (f κ : ℝ → ℝ)
    (hκ : ContinuousOn κ (Ioi (0 : ℝ)))
    (hslope : ∀ a b : ℝ, 0 < a → 0 < b → a ≠ b →
      min (κ a) (κ b) ≤ slope f a b ∧
        slope f a b ≤ max (κ a) (κ b)) :
    ∀ a : ℝ, 0 < a → HasDerivAt f (κ a) a := by sorry
