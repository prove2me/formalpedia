-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_weak_HJB_positive_reserve_drift_negative_mark_ceiling
-- name    : AvramDividend.Classical.avram_bvb_weak_HJB_positive_reserve_drift_negative_mark_ceiling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:58:54.380708+00:00
-- url     : https://prove2.me/theorems/7895009e-2095-48da-8c85-84b281247082
-- title:
--   Original Standing BV positive-reserve HJB and gradient bound imply compensated drift-plus-negative-mark ceiling
-- statement:
--   For every Standing spectrally negative bounded-variation Lévy process, the original HJB generator upper inequality and positive-region derivative lower bound of one imply that the physical positive drift plus full original negative-jump integral minus discounted candidate reward is nonpositive at every strictly interior reserve. This is the sound positive-reserve algebraic premise for proving the weak zero-boundary HJB sign by a one-sided limit.
-- source:
--   Use Proved Standing BV drift positivity and exact generator representation to lower bound generator drift by the physical drift, then apply the original HJB inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_weak_HJB_positive_reserve_drift_negative_mark_ceiling
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y : ℝ) (hy : 0 < y) (hyC : ENNReal.ofReal y < C) :
    X.drift +
      (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) -
      q * w y ≤ 0 := by sorry
