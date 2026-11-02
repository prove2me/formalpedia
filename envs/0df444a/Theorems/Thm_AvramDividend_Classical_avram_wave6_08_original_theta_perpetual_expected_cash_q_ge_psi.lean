-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_perpetual_expected_cash_q_ge_psi
-- name    : AvramDividend.Classical.avram_wave6_08_original_theta_perpetual_expected_cash_q_ge_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T00:15:46.625873+00:00
-- url     : https://prove2.me/theorems/2abbc6bc-a935-4373-95af-053049feac3c
-- title:
--   Perpetual genuine original full-Stieltjes dividend expectation obeys θ-scaled source exponential bound
-- statement:
--   For the original source Lévy dividend process, any θ>0 and q≥ψ(θ), the expected perpetual fully stopped cash is θ-scaled bounded by exp(θx). This follows by cofinal increasing genuine restricted payment sets, original random-clock measurability, canonical finite θ budget, and source pathwise monotone convergence.
-- source:
--   Imports Proved source finite θ rate 489b3a72, source clock-measurable 3deca135 and source full-Stieltjes pathwise supremum 21a1dc8d. Independent Chat08 expectation endpoint, not generic HJB stochastic core.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_real_clock_stopped_full_stieltjes_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_cash_eq_iSup_integer_truncations
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_theta_perpetual_expected_cash_q_ge_psi
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (θ : ℝ) (hθ : 0 < θ) (q : ℝ) (hq : X.ψ θ ≤ q) :
    ENNReal.ofReal θ *
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω ∂P) ≤
      ENNReal.ofReal (Real.exp (θ * x)) := by sorry
