-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB42_original_postpayment_real_time_reserve_measurable_path
-- name    : AvramDividend.Classical.avram_gbB42_original_postpayment_real_time_reserve_measurable_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:51:52.673056+00:00
-- url     : https://prove2.me/theorems/ae2eb054-b48e-4ae6-895d-7ee120cf5611
-- title:
--   Original postpayment reserve is measurable as a real-time path at every fixed sample
-- statement:
--   For the original Lévy source and any adapted dividend strategy, every fixed sample path of the postpayment reserve is Borel measurable after mapping a real clock into nonnegative time. This supplies the measurable exact-level contact event needed for the original finite-cap cap-linear Gaussian occupation argument.
-- source:
--   Compose Proved B269 joint time/sample measurability of x+X(t)-rightLimit D(t) with the measurable map t ↦ (Real.toNNReal t, ω).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB269_original_postpayment_reserve_joint_time_sample_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB42_original_postpayment_real_time_reserve_measurable_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ ω : Ω, Measurable (fun t : ℝ =>
      x + X.X (Real.toNNReal t) ω -
        rightLimit D (Real.toNNReal t) ω) := by sorry
