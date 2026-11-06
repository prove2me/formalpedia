-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_cofinal_strict_terminal_budget_real_mean
-- name    : AvramDividend.Classical.avram_limit2_cofinal_strict_terminal_budget_real_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:16:46.635762+00:00
-- url     : https://prove2.me/theorems/2373fd16-4783-497e-8598-5ca90f7b6d52
-- title:
--   Original strict cofinal stopped budgets to genuine real perpetual signed Stieltjes payout
-- statement:
--   Every strictly cofinal deterministic open real horizon family T:ℕ→ℝ whose original genuine Stieltjes cash on paymentTimes(ruinTime)∩Iio(T k) plus arbitrary nonnegative terminal has an expected upper bound ENNReal.ofReal B yields full original dividendValue≤ofReal B, integrable real signed Stieltjes payout, exact ENNReal.ofReal expected real cash identity and real cash mean≤B, assuming B≥0. This preserves time-zero and finite right-horizon atoms through strict cofinality without terminal vanishing.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_arbitrary_strict_cofinal_horizon_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_perpetual_real_cash_mean_le_of_value_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_cofinal_strict_terminal_budget_real_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (T : ℕ → ℝ) (hT : ∀ a : ℝ, ∃ k : ℕ, a < T k)
    (B : ℝ) (hB : 0 ≤ B)
    (hBudget : ∀ k : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T k),
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
