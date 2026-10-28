-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_dividend_grid_verification_of_integrable_cash_budget
-- name    : AvramDividend.Classical.stopped_dividend_grid_verification_of_integrable_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:59:49.6852+00:00
-- url     : https://prove2.me/theorems/5061512e-30ef-4980-bf93-36cacb6b9a0d
-- title:
--   Exact stopped Stieltjes dividend verification under integrable conditional cash
-- statement:
--   For any admissible dividend process and stopping-at-ruin payout, if each exact discounted half-open interval Stieltjes cash amount is integrable, terminal values are integrable with nonnegative expected terminal contribution, and a genuine conditional one-step stochastic HJB budget holds for future-dependent cash, then the full expected capped stopped Stieltjes dividend reward is at most the initial candidate value. This removes the stronger requirement to integrate all dividends D(T+1), including any post-ruin cash. It imports the proved conditional Levy-grid cash limit and pathwise Stieltjes partition, and directly serves both bounded and unbounded variation capped stochastic verification leaves.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.Finset.Range
import Theorems.Thm_AvramDividend_Classical_exponential_levy_grid_cash_stieltjes_limit_le_initial
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_dividend_payout_eq_iSup_unit_cash_toReal_of_strategy
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_real_cash_prefix_measurable_of_strategy
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_cash_prefixes_nonnegative_monotone
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stopped_dividend_grid_verification_of_integrable_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (hs0 : s 0 = 0)
    (u cash : ℕ → Ω → ℝ) (w : ℝ → ℝ) (q x : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0)
    (hCashEq : ∀ (k : ℕ) (ω : Ω), cash k ω =
      (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩ Ico (k : ℝ) ((k : ℝ) + 1),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
    (hCashI : ∀ k, Integrable (cash k) P)
    (hu0 : ∀ᵐ ω ∂P, u 0 ω = x)
    (hVI : ∀ k, Integrable (fun ω => Real.exp (-(q * (s k : ℝ))) * w (u k ω)) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      (P[(cash k) | 𝓕 (s k)]) ω +
      (P[(fun η => Real.exp (-(q * (s (k + 1) : ℝ))) * w (u (k + 1) η)) | 𝓕 (s k)]) ω ≤
      Real.exp (-(q * (s k : ℝ))) * w (u k ω))
    (hterminal : ∀ n : ℕ, 0 ≤ ∫ ω, Real.exp (-(q * (s n : ℝ))) * w (u n ω) ∂P) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by sorry
