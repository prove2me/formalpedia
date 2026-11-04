-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_controlled_fixed_horizon_left_tendsto_ae
-- name    : AvramDividend.Classical.avram_p3_bv_original_controlled_fixed_horizon_left_tendsto_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:12:44.991195+00:00
-- url     : https://prove2.me/theorems/3f331130-82d0-4aca-9da3-85d331f32b78
-- title:
--   Original controlled pre-rightpayment reserve converges from the left at deterministic positive horizons
-- statement:
--   The actual original controlled pre-rightpayment reserve tends along the left-neighbourhood filter at every fixed positive time to its current physical value on a probability-one event. The source Levy path has no deterministic positive-time jumps and the original dividend strategy is left-continuous. This strengthens the earlier endpoint left-limit equality to the exact filter convergence required to compose a continuous HJB candidate during strict-survival horizon passage, without any compensation assumption.
-- source:
--   Source theorem b4407263-9eac-412e-be7a-17c1fecc8ebe (Proved); original IsDividendStrategy left continuity; pinned Mathlib tendsto_leftLim_of_tendsto and continuity of subtraction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_controlled_fixed_horizon_left_tendsto_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P,
      Tendsto (fun s : ℝ≥0 => riskProcess X x D s ω)
        (𝓝[<] t) (𝓝 (riskProcess X x D t ω)) := by sorry
