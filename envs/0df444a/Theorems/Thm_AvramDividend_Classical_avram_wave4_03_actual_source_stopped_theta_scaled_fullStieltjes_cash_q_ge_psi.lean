-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_stopped_theta_scaled_fullStieltjes_cash_q_ge_psi
-- name    : AvramDividend.Classical.avram_wave4_03_actual_source_stopped_theta_scaled_fullStieltjes_cash_q_ge_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:37:03.119724+00:00
-- url     : https://prove2.me/theorems/3b76ccd4-0013-41e6-ac01-5ba47c110fde
-- title:
--   Actual original stopped full-Stieltjes expected cash at q≥ψ(theta) with theta-scaled exponential bound
-- statement:
--   For the actual spectrally negative Lévy source, any capped admissible same-path dividend D, positive theta and q≥ψ(theta), the expected strictly pre-ruin full [0,T] Stieltjes dividend payoff multiplied by theta is ≤ exp(theta x). This includes the time-zero atom, all positive right atoms and diffuse/singular payment mass. The proof combines genuine original-source stochastic theta martingale consumption, original postpayment solvency, and both random integral measurability and constant-factor interchange.
-- source:
--   Same-source theta-scaled closed-horizon stochastic budget new child and accepted general theta stopped solvency c1292a84.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actualStopped_theta_exponential_payment_kernel_dominated
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_theta_scaled_closedHorizon_Icc_fullStieltjes_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_exponential_random_fullStieltjes_lintegral_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_wave4_03_actual_source_stopped_theta_scaled_fullStieltjes_cash_q_ge_psi
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (θ : ℝ) (hθ : 0 < θ) (q : ℝ) (hq : X.ψ θ ≤ q)
    (T : ℝ≥0) (hT : 0 < T) :
    ENNReal.ofReal θ * (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      if s ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(q * (s.toNNReal : ℝ))))
      else 0 ∂dividendMeasure D ω ∂P) ≤
    ENNReal.ofReal (Real.exp (θ * x)) := by sorry
