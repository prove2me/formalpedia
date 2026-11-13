-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB211_continuous_gradient_compact_clip_Borel_measurable
-- name    : AvramDividend.Classical.avram_gbB211_continuous_gradient_compact_clip_Borel_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:41:49.249903+00:00
-- url     : https://prove2.me/theorems/da7ce994-e6d7-4abb-8186-2ea912e4c099
-- title:
--   Continuous compact-band clipped reward derivative is Borel measurable for any selected interior thresholds
-- statement:
--   If the reward gradient is continuous on a finite closed clipping interval, then the piecewise function equal to that gradient inside the interval and one outside is Borel measurable on the whole real line.
-- source:
--   Generic original Gaussian clipping measurability for selected good boundaries B205, from Proved B134 method; complements compact uniform bound B210.

import Mathlib
open MeasureTheory Set Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB211_continuous_gradient_compact_clip_Borel_measurable
    (w : ℝ → ℝ) (a b : ℝ)
    (hContinuous : ContinuousOn (deriv w) (Icc a b)) :
    Measurable (fun y : ℝ =>
      if y ∈ Icc a b then deriv w y else 1) := by sorry
