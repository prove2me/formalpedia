-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_predictable_integrable_physical_time_fibre
-- name    : AvramDividend.Classical.avram_ubv_top9_predictable_integrable_physical_time_fibre
-- status  : Open
-- author  : @WillR
-- created : 2026-11-07T17:54:24.786887+00:00
-- url     : https://prove2.me/theorems/53f00d00-bd8d-4382-a636-1e658297e38b
-- title:
--   Predictable drift integrability transfers to the original physical time-fibre integral
-- statement:
--   If a finite predictable measure agrees on every predictable event with the actual restricted physical time-law product P and the original generator drift is integrable in that predictable measure, the fibrewise physical time integral is integrable on P. Uses exactly the source filtration and no independent surrogate process.
-- source:
--   Pinned Mathlib Measure.trim_measurableSet_eq, integrable_of_integrable_trim, Integrable.integral_prod_right. Potential bridge from ca1e7b57 to 0560d7c6 and original infinite-cap witness 25573e81; no strengthening of original HJB.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_predictable_integrable_physical_time_fibre
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (T : ℝ≥0) (R : ℝ≥0 × Ω → ℝ)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμeq : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (hR : Integrable R μ) :
    Integrable (fun ω : Ω =>
      ∫ t : ℝ≥0, R (t, ω) ∂
        (((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal)) P := by sorry
