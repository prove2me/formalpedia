-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_excess30_original_discounted_prepayment_surviving_horizon_left_limit
-- name    : AvramDividend.Classical.avram_bv_excess30_original_discounted_prepayment_surviving_horizon_left_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:55:35.06719+00:00
-- url     : https://prove2.me/theorems/7420c238-4fab-4b84-9073-9cbe42165c2c
-- title:
--   Actual surviving original BV discounted prepayment terminal is the strict-left horizon limit
-- statement:
--   For the actual spectrally negative Levy source with its original left-continuous dividend control, at any fixed deterministic positive horizon strictly before ruin, the discounted prepayment reward is the left limit of its original controlled-reserve reward. This uses the Proved no-fixed-time source jump, dividend left-continuity, strict pre-ruin nonnegative reserves and the original candidate continuity only on [0,∞). It is the genuine missing endpoint correction in 4f605d76 and does not assume zero-jump ν or any generator B L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_excess30_original_discounted_prepayment_surviving_horizon_left_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (q : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ((T : ℝ≥0∞) < ruinTime X x D ω) →
      Filter.Tendsto
        (fun s : ℝ≥0 =>
          Real.exp (-(q * (s : ℝ))) * w (riskProcess X x D s ω))
        (𝓝[<] T)
        (𝓝 (Real.exp (-(q * (T : ℝ))) *
          w (riskProcess X x D T ω))) := by sorry
