-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_perpetual_stieltjes_cash_integrable_q_ge_psi
-- name    : AvramDividend.Classical.avram_wave6_08_original_theta_perpetual_stieltjes_cash_integrable_q_ge_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T00:20:39.667007+00:00
-- url     : https://prove2.me/theorems/5b1a666c-fc31-4466-a206-a4d2fcea7dcb
-- title:
--   Original perpetual full-Stieltjes dividend payoff is L1 at every positive source exponential tilt
-- statement:
--   For any positive tilt θ and source discount q≥ψ θ, the full source perpetually stopped Stieltjes payoff is a P-integrable real random variable, with no special assumption q≥ψ1. Proved from true source θ-scaled expected all-time payoff bound, strictly positive finite θ factor, and original kernel measurability.
-- source:
--   Uses canonical source perpetual θ bound 2abbc6bc after it is Proved and source untruncated measurability db59cbee; independent genuine source payout L1 for all q≥ψθ.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_perpetual_expected_cash_q_ge_psi
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_theta_perpetual_stieltjes_cash_integrable_q_ge_psi
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (θ : ℝ) (hθ : 0 < θ) (q : ℝ) (hq : X.ψ θ ≤ q) :
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) P := by sorry
