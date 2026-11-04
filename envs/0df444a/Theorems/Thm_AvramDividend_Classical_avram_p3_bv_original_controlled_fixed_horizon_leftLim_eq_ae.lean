-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_controlled_fixed_horizon_leftLim_eq_ae
-- name    : AvramDividend.Classical.avram_p3_bv_original_controlled_fixed_horizon_leftLim_eq_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:35:55.636486+00:00
-- url     : https://prove2.me/theorems/50564343-1f4f-41e4-a1ce-29faafbed9f9
-- title:
--   Original controlled pre-rightpayment reserve has no deterministic positive-time left jump almost surely
-- statement:
--   For the original spectrally negative Levy process and an original dividend strategy, at each fixed positive horizon t the controlled pre-rightpayment reserve riskProcess X x D has its left limit equal to its value almost surely. This follows from the source no-fixed-jump theorem and pathwise left continuity of the dividend strategy. It is an endpoint convergence helper for BV stopped verification and does not assume any compensation law.
-- source:
--   Direct proof from Proved original no-fixed-jump theorem b4407263-9eac-412e-be7a-17c1fecc8ebe and the source IsDividendStrategy.left-continuity component using pinned Mathlib LeftRightLim lemmas.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_controlled_fixed_horizon_leftLim_eq_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P,
      Function.leftLim (fun s : ℝ≥0 => riskProcess X x D s ω) t =
        riskProcess X x D t ω := by sorry
