-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_uniform_count_L2
-- name    : AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_uniform_count_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:53:13.088817+00:00
-- url     : https://prove2.me/theorems/d6906ce2-551e-411f-a4ca-ba6c62420cdb
-- title:
--   Original finite-negative-activity cutoff count has a uniform physical L2 budget
-- statement:
--   For a finite negative Levy intensity, the original physical negative-jump cutoff count has a quadratic expectation bounded by total finite intensity R squared plus R, uniformly in the cutoff. Unlike pointwise finite-cutoff square integrability, this provides a cutoff-independent integrable-size budget required for physical compensated small-jump L2 limits.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_marked_negative_subband_explicit_quadratic_budget

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_uniform_count_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let R : ℝ := ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal
    Integrable (fun ω => (N ω).toReal ^ 2) P ∧
      (∫ ω, (N ω).toReal ^ 2 ∂P) ≤ R ^ 2 + R := by sorry
