-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_cofinal_closed_terminal_budget_real_mean
-- name    : AvramDividend.Classical.avram_limit2_cofinal_closed_terminal_budget_real_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:15:34.732816+00:00
-- url     : https://prove2.me/theorems/f93fdf4d-3650-424a-a45d-5703aaf9c443
-- title:
--   Actual original perpetual real Stieltjes value from positive closed cofinal cash and terminal budgets
-- statement:
--   For any cofinal deterministic real horizon schedule, expected genuine original discounted Stieltjes cash through Iic(T k) plus arbitrary nonnegative ENNReal terminal is bounded by finite real B uniformly in k. Exact arbitrary-cofinal horizon exhaustion gives full original dividendValue≤ENNReal.ofReal B. Source finite value theorem yields L1 original signed Stieltjes payout, exact expectation equality and a real mean bound ≤B. The arbitrary deterministic cofinal schedule need not be monotone; zero and endpoint atoms are retained. No terminal vanishing or equality in law.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_arbitrary_cofinal_closed_horizon_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_perpetual_real_cash_mean_le_of_value_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_cofinal_closed_terminal_budget_real_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (T : ℕ → ℝ) (hT : ∀ a : ℝ, ∃ k : ℕ, a ≤ T k)
    (B : ℝ) (hB : 0 ≤ B)
    (hBudget : ∀ k : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T k),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤
        ENNReal.ofReal B) :
    dividendValue X q x D ≤ ENNReal.ofReal B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal (∫ ω,
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B := by sorry
