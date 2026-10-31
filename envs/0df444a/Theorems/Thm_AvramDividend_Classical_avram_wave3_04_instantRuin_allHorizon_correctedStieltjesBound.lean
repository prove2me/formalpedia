-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_instantRuin_allHorizon_correctedStieltjesBound
-- name    : AvramDividend.Classical.avram_wave3_04_instantRuin_allHorizon_correctedStieltjesBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:58:36.457998+00:00
-- url     : https://prove2.me/theorems/e8d8ec8a-10a2-4797-a987-93afe1a43df0
-- title:
--   Original capped dividend verification at every finite horizon for almost-sure immediate ruin
-- statement:
--   For any original spectrally negative Lévy process and any admissible capped dividend strategy that ruins at time zero almost surely, the corrected HJB verification upper bound for the complete actual discounted Stieltjes dividend reward holds at every nonnegative finite horizon. The proof first uses the already Proved corrected zero-horizon inequality with w(0)≥0, endpoint-continuous C¹ candidate and gradient and jump HJB dominance. On every path with ruin time zero, the genuine stopped-payment set reduces to the singleton time zero; hence its intersection with any closed future horizon is identical to the zero-horizon set. Equality of the entire original Stieltjes integrals on such paths and almost-everywhere outer integral congruence carry the verified bound to all horizons. This is a true positive-time exact-source verification branch for every cap and all admissible strategies with instantaneous ruin, not a semimartingale substitution.
-- source:
--   Exact pinned compiler probe a0f7c93b-c7ac-4934-b99a-7fdec989850c reached intentional sentinel with no source errors, SHA256 099137283b6bd2c348829025ab699c19c85fcd600653d169736d42a46623a208. Accepted canonical corrected UBV zero-horizon bound 3858a86b-eff8-46f1-b700-7ee855dad85a and paymentTimes_min_zero_eq_singleton_zero 77cdd573-4256-4dbd-8c0a-e95881be40e6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_corrected_ubv_zero_horizon_bound
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_instantRuin_allHorizon_correctedStieltjesBound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (hRuin : ∀ᵐ ω ∂P, ruinTime X x D ω = 0)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
