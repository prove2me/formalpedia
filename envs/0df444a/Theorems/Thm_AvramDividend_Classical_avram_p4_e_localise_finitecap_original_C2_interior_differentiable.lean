-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_finitecap_original_C2_interior_differentiable
-- name    : AvramDividend.Classical.avram_p4_e_localise_finitecap_original_C2_interior_differentiable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:47:42.567014+00:00
-- url     : https://prove2.me/theorems/89aae9b0-d294-459c-b773-5219563689b5
-- title:
--   Actual ENNReal-capped interior C² implies differentiability on finite real cap interior
-- statement:
--   Transport the canonical original C² smoothness on {y|0<y∧ENNReal.ofReal y<ENNReal.ofReal c} to DifferentiableOn ℝ w (Ioo 0 c). The strict ENNReal endpoint inequality is equivalent to real strict interior inequalities because c is positive at each interior point. Mathlib ContDiffOn.differentiableOn supplies the derivative interface needed by the finite-cap positivity/monotonicity helper. No changed theorem premises.
-- source:
--   Mathlib.Analysis.Calculus.ContDiff.Defs ContDiffOn.differentiableOn; Mathlib.Basic.ENNReal.Real ofReal_lt_ofReal_iff'.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- The exact original ENNReal-capped interior C² hypothesis implies real-interval differentiability. -/
theorem AvramDividend.Classical.avram_p4_e_localise_finitecap_original_C2_interior_differentiable
    (w : ℝ → ℝ) (c : ℝ)
    (hwSmooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c}) :
    DifferentiableOn ℝ w (Ioo (0 : ℝ) c) := by sorry
