-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_real_clock_stopped_full_stieltjes_budget
-- name    : AvramDividend.Classical.avram_wave6_08_original_theta_real_clock_stopped_full_stieltjes_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T00:09:47.819197+00:00
-- url     : https://prove2.me/theorems/489b3a72-e3e6-4fab-af24-caa43e7fc396
-- title:
--   Actual original finite real-clock θ-scaled Stieltjes reward bound for q≥ψ(θ)
-- statement:
--   For any original admissible capped spectrally negative Lévy dividends, θ>0 and q≥ψ(θ), the expected complete Stieltjes reward on the true real-time paymentTimes∩Iic T is θ-weightedly bounded by exp(θx). All payments are on the original sample space and genuine dividend measure; no Gaussian/jump representation assumption is introduced.
-- source:
--   Proved original-source θ-scaled full-Icc budget 3b76ccd4 and source chronological reward restriction 122d4c4b, exact conversion from accepted proof 1694b09e. Independent real-clock exponential-rate original source API, not the arbitrary w stochastic core 429e17ca.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_stopped_theta_scaled_fullStieltjes_cash_q_ge_psi
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_stopped_original_reward_eq_closed_horizon_restriction
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_wave6_08_original_theta_real_clock_stopped_full_stieltjes_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (θ : ℝ) (hθ : 0 < θ) (q : ℝ) (hq : X.ψ θ ≤ q)
    (T : ℝ≥0) (hT : 0 < T) :
    ENNReal.ofReal θ *
      (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂dividendMeasure D ω ∂P) ≤
    ENNReal.ofReal (Real.exp (θ * x)) := by sorry
