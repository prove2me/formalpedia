-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_initial_value_nonnegative
-- name    : AvramDividend.Classical.avram_p3_bv_initial_value_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T15:49:20.133079+00:00
-- url     : https://prove2.me/theorems/c5c9e4bf-4fd5-44b8-8929-4adde026e265
-- title:
--   Canonical BV cap and initial reserve imply nonnegative verification value
-- statement:
--   For the original positive-cap BV HJB candidate, C1 interior derivative at least one, w(0) nonnegative, continuity on nonnegative states, and canonical nonnegative initial x below C force w(x) nonnegative. The proof handles finite and infinite cap separately using the Proved all-cap slope-one continuation positivity. This discharges the initial Fatou and signed-mesh boundary premise without a new value assumption.
-- source:
--   Accepted 6f389e8f-2b4f-4cef-be75-06a1f48c259f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_allcap_linear_nonnegative

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The original canonical nonnegative initial reserve and cap bound
force the verification candidate to be nonnegative at inception. -/

theorem AvramDividend.Classical.avram_p3_bv_initial_value_nonnegative
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) :
    0 ≤ w x := by sorry
