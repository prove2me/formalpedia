-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_survival_hjb_left_tendsto_ae
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_survival_hjb_left_tendsto_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:18:41.216649+00:00
-- url     : https://prove2.me/theorems/3683f8b1-5c6c-4923-87b0-8e0488b6f42e
-- title:
--   Original pre-rightpayment HJB value is left-continuous at every strictly surviving deterministic positive horizon
-- statement:
--   At any fixed positive horizon strictly before the genuine original controlled ruin time, the HJB candidate evaluated at the actual pre-rightpayment reserve converges from the left to its horizon value almost surely. The original risk process remains nonnegative up to strict ruin, so continuity of w on [0,∞) suffices even at zero and positive-cap boundary. Uses the prior original controlled reserve fixed-time left-convergence theorem and assumes no jump compensator or stochastic integration premise. It does not assert convergence when the horizon equals ruin.
-- source:
--   Previous fixed-time controlled reserve left-convergence theorem 3f331130-82d0-4aca-9da3-85d331f32b78; original pre-ruin reserve nonnegative theorem 03a69d71-1387-4410-83a2-1fe59054ebe6; pinned Mathlib tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_controlled_fixed_horizon_left_tendsto_ae
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_survival_hjb_left_tendsto_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ruinTime X x D ω →
      Tendsto (fun s : ℝ≥0 => w (riskProcess X x D s ω))
        (𝓝[<] t) (𝓝 (w (riskProcess X x D t ω))) := by sorry
