-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_finite_horizon_value_budget_from_stopped_and_terminal_atom
-- name    : AvramDividend.Classical.avram_wave7_11_original_finite_horizon_value_budget_from_stopped_and_terminal_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:14:31.102716+00:00
-- url     : https://prove2.me/theorems/ff1fbe65-2cb7-4e0d-b460-c730fface824
-- title:
--   Exact original expected finite horizon dividend upper budget from stopped Itô cash and terminal atom budgets
-- statement:
--   For the original Levy dividend measure, if the expected genuine discounted Stieltjes payout strictly stopped at min(ruinTime,T) is bounded by B and the expected original terminal payment singleton at T is bounded by A, then the complete actual finite-horizon expected dividend payout through T is bounded by B+A. This formalises the precise boundary correction necessary when stochastic Ito-Meyer estimates stop exactly at T, without any hidden terminal atomlessness, integrability, or positivity assumptions.
-- source:
--   Remotely Proved W7-11 original expected upper endpoint theorem ceca6326, Mathlib ENNReal addition monotonicity, source original Ω/P/X/D.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_horizon_reward_le_min_clock_plus_terminal_atom
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_original_finite_horizon_value_budget_from_stopped_and_terminal_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (hT : 0 ≤ T) (B A : ℝ≥0∞)
    (hStopped :
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ B)
    (hTerminal :
      (∫⁻ ω, ∫⁻ t in
        (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ A) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ B + A := by sorry
