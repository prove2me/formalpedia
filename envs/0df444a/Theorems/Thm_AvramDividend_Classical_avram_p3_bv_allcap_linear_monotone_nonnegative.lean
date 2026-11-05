-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_allcap_linear_monotone_nonnegative
-- name    : AvramDividend.Classical.avram_p3_bv_allcap_linear_monotone_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:38:26.669919+00:00
-- url     : https://prove2.me/theorems/56a6e05f-9444-42a9-9634-8913b2254b0a
-- title:
--   Canonical BV HJB cap-linear continuation is monotone on nonnegative reserves at all caps
-- statement:
--   Under the canonical original BV HJB candidate continuity and derivative-bound hypotheses, the slope-one cap-linear continuation is monotone on the entire nonnegative real line for every positive cap, finite or infinite. This includes zero and finite-cap contact without smooth fit or differentiability above the cap. It follows from the stronger globally Proved dividend secant `5907ddca`, and gives a source-independent order property of the verification candidate for subsequent Stieltjes/finite-variation controlled-path arguments.
-- source:
--   Proved all-cap global dividend secant 5907ddca-d6f1-4ea3-9879-e7f3a6b91707, plus real arithmetic, makes V(b)-V(a)≥b-a≥0 whenever 0≤a≤b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_allcap_linear_global_secant

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_allcap_linear_monotone_nonnegative
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    MonotoneOn (fun z : ℝ =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)) (Ici 0) := by sorry
