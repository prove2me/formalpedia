-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_weighted_log_positive_band_test
-- name    : AvramDividend.Classical.avram_p2_i_moment_weighted_log_positive_band_test
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:34:35.960937+00:00
-- url     : https://prove2.me/theorems/c2941450-85ba-4203-9f6b-649e7339220b
-- title:
--   Original negative-mark weighted logarithmic test satisfies positive-band support conditions
-- statement:
--   For a continuous negative-mark test f supported below a strictly negative upper mark and above a finite lower mark, the all-real logarithmic weighted transform g(z)=f(log z)/(z-1)^4 is continuous. On the nonnegative half-line it vanishes throughout [0,exp(a)/2] and [1,∞). The transformed g may take nonzero values for negative z under Lean's Real.log convention, so it is suitable for the new P2-I positive-band test theorem rather than falsely assuming support in (0,1). This helper packages only already Proved P2-B continuity and band-support results.

import Mathlib
open MeasureTheory Filter Topology Set

theorem AvramDividend.Classical.avram_p2_i_moment_weighted_log_positive_band_test
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0) :
    Continuous (fun z : ℝ => f (Real.log z) / (z - 1) ^ 4) ∧
    ∃ δ : ℝ, 0 < δ ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ δ →
        f (Real.log z) / (z - 1) ^ 4 = 0) ∧
      (∀ z : ℝ, 1 ≤ z →
        f (Real.log z) / (z - 1) ^ 4 = 0) := by sorry
