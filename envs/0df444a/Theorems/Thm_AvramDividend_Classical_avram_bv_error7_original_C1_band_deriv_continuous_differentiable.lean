-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_C1_band_deriv_continuous_differentiable
-- name    : AvramDividend.Classical.avram_bv_error7_original_C1_band_deriv_continuous_differentiable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:45:00.130085+00:00
-- url     : https://prove2.me/theorems/7cd447b9-8d95-479d-936a-a8ac92223d74
-- title:
--   Original dividend C1 value function has continuous derivative and differentiability on every compact strict-cap band
-- statement:
--   For the actual C1 value function w on the open original positive subcap domain {0<y, ofReal y<C}, every real compact interval contained in that domain inherits continuity of deriv w and differentiability of w at each of its points. The openness assumption allows the differentiable-within domain conclusion to become DifferentiableAt. This is the source-exact adapter required to apply compact real mean-value and derivative-bounded estimates to the actual bounded-variation dividend source cells.
-- source:
--   Pinned Mathlib ContDiffOn.differentiableOn_one, ContDiffOn.continuousOn_deriv_of_isOpen, DifferentiableWithinAt.differentiableAt of IsOpen.mem_nhds. Original C1 hypotheses are the exact ones used by avram_p3_f2_original_discounted_BV_physical_mesh_errors_vanish 46049abe and BV-ERROR7 interior Taylor theorem d7008b37. No budgets or stochastic expectations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_C1_band_deriv_continuous_differentiable
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ContinuousOn (deriv w) (Set.Icc a b) ∧
      (∀ y ∈ Set.Icc a b, DifferentiableAt ℝ w y) := by sorry
