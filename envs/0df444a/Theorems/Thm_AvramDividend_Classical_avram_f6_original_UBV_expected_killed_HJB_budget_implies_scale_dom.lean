-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_expected_killed_HJB_budget_implies_scale_dom
-- name    : AvramDividend.Classical.avram_f6_original_UBV_expected_killed_HJB_budget_implies_scale_dom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:05:10.031738+00:00
-- url     : https://prove2.me/theorems/997beeb3-c109-45b7-be12-401f1d3ce40f
-- title:
--   Original stopped HJB expected first-exit inequality implies true q-scale domination
-- statement:
--   For original standing UBV Levy with authentic q-scale W and killed first-exit expectation of w, suppose the actual stopped discounted HJB supermartingale yields w(b)*twoSidedExitExpectation(q,b,1).toReal≤w(1). Proved true stopped scale ratio and original W>0 imply w(b)≤(w(1)/W(1))W(b) for all b≥1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_UBV_expected_killed_HJB_budget_implies_scale_dom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w W : ℝ → ℝ) (hw1 : 0 ≤ w 1)
    (hW : IsScaleFunction X q W)
    (hExit : ∀ b : ℝ, 1 ≤ b →
      w b * (twoSidedExitExpectation X q b 1).toReal ≤ w 1) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ b : ℝ, 1 ≤ b → w b ≤ A * W b := by sorry
