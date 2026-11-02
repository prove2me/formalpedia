-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_compact_clamped_quotient_continuity
-- name    : AvramDividend.Classical.avram_wave5_04c_compact_clamped_quotient_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:13:51.462591+00:00
-- url     : https://prove2.me/theorems/7e8fa8ea-cc79-4668-8116-b25c3a5b5092
-- title:
--   Continuous compact quotient data extends to unit interval by a clamp
-- statement:
--   A continuous function on the compact interval [a,1] can be transported to a continuous function on [0,1] by clamping its argument to [a,1]. This supports extending the original C1 payoff logarithmic quotient from t≥exp(-M) to a full domain where weighted polynomial approximation applies, without evaluating log at t=0.
-- source:
--   Continuity of min/max and ContinuousOn.comp; input will be the proven C1 extended difference quotient.

import Mathlib
set_option autoImplicit false
open Set

theorem AvramDividend.Classical.avram_wave5_04c_compact_clamped_quotient_continuity
    (f : ℝ → ℝ) (a : ℝ) (ha : a ≤ 1)
    (hf : ContinuousOn f (Set.Icc a 1)) :
    ContinuousOn (fun t : ℝ => f (max a (min t 1))) (Set.Icc 0 1) := by sorry
