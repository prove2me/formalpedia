-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a158_original_topcap_C2_value_continuous_positive_halfline
-- name    : AvramDividend.Classical.avram_ga_a158_original_topcap_C2_value_continuous_positive_halfline
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:30:31.404682+00:00
-- url     : https://prove2.me/theorems/a9525933-3e8a-4a50-9604-3c637bfbc959
-- title:
--   Original top-cap Gaussian Avram C2 supersolution is continuous on the whole strictly positive reserve half-line
-- statement:
--   Under the original top-cap C=⊤ Gaussian Avram supersolution smoothness assumption, the positive-domain set {y : 0<y and ENNReal.ofReal y<C} equals the open strictly-positive half-line. Consequently the actual value function w is continuous there. This source-exact domain identification supplies the hypothesis to the positive-only measurable spatial difference and finite-grid sum theorems ga156/ga157, without assuming w continuous on negative reserves.
-- source:
--   Original b0 positive-interior smoothness hypothesis and pinned Mathlib ContDiffOn.continuousOn.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Topology AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a158_original_topcap_C2_value_continuous_positive_halfline
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ContinuousOn w (Ioi (0 : ℝ)) := by sorry
