-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_fixed_time_L1
-- name    : AvramDividend.Classical.avram_bv_residual10_original_raw_R_fixed_time_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:42:24.628713+00:00
-- url     : https://prove2.me/theorems/cac67b8e-79eb-4b55-a427-40aa74a3a142
-- title:
--   Original BV raw real-jump remainder is integrable at any fixed horizon
-- statement:
--   The genuine real raw-jump drift remainder of the original bounded-variation spectrally negative Levy source is integrable at every fixed time under Standing. Its almost-sure monotonicity and zero anchor make it nonnegative, while the pathwise nonnegative original left-jump sum bounds it above by the original drift-minus-position endpoint, which is L1 at every finite time by the already Proved source theorem. The original raw remainder is a.e. measurable by a separate proved coordinate theorem. This supplies an integrable finite-horizon envelope for bounded predictable stopped weights without any Brownian isometry or law substitution.
-- source:
--   AVRAM BV-RESIDUAL10 fixed-time original-source L1 bridge from Proved raw monotonicity, original jump sign, original X L1 and original raw R measurability, 7 November 2026

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_ae_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_X_integrable_any_clock
import Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_original_raw_R_coordinate_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_raw_R_fixed_time_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation) (T : ℝ≥0) :
    Integrable (fun ω =>
      ((T : ℝ) * X.drift - X.X T ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ T then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)) P := by sorry
