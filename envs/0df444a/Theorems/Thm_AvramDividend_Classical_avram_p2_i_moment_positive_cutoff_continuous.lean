-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_positive_cutoff_continuous
-- name    : AvramDividend.Classical.avram_p2_i_moment_positive_cutoff_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:31:02.577086+00:00
-- url     : https://prove2.me/theorems/3d0ce95d-e704-4991-b5d8-cf813131d359
-- title:
--   Continuous positive-halfline cutoff preserving tests that vanish near zero
-- statement:
--   Given a continuous real test g that is zero on [0,δ] for some δ>0 and on [1,∞), construct a continuous real u using the linear ramp min(1,max(0,z/δ)) times g. The resulting u vanishes everywhere outside (0,1) while agreeing with g at every nonnegative argument. The source-specific P2-B logarithmic weighted test is continuous but can be nonzero at negative z because Real.log uses |z|, so this deterministic cutoff is necessary for the existing P2-I theorem's zero-outside hypothesis without changing any positive exponential-image integrals.

import Mathlib
open MeasureTheory Filter Topology Set

theorem AvramDividend.Classical.avram_p2_i_moment_positive_cutoff_continuous
    (g : ℝ → ℝ) (hg : Continuous g)
    (δ : ℝ) (hδ : 0 < δ)
    (hzero_small : ∀ z : ℝ, 0 ≤ z → z ≤ δ → g z = 0)
    (hzero_upper : ∀ z : ℝ, 1 ≤ z → g z = 0) :
    ∃ u : ℝ → ℝ,
      Continuous u ∧
      (∀ z : ℝ, z ≤ 0 ∨ 1 ≤ z → u z = 0) ∧
      (∀ z : ℝ, 0 ≤ z → u z = g z) := by sorry
