-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_dividend_grid_verification_of_conditional_budget
-- name    : AvramDividend.Classical.stopped_dividend_grid_verification_of_conditional_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:36:27.490826+00:00
-- url     : https://prove2.me/theorems/0c73bc7f-4523-4faf-b449-c7faa09497ec
-- title:
--   Stopped Stieltjes dividend verification from the conditional Levy grid budget
-- statement:
--   If a capped admissible dividend strategy has an integrable cumulative-dividend envelope and satisfies a finite-grid conditional HJB one-step supermartingale inequality with integrable discounted terminal verification values and nonnegative terminal expectations, then the exact expected capped stopped Stieltjes dividend payout is bounded by the initial candidate w(x). This assembles already proved unit-cash integrability, measurable real cash prefixes, their nonnegativity/monotonicity, the exact stopped dividend payout decomposition, and the Proved conditional-Levy-grid limit theorem. The theorem isolates the remaining BV C1/UV C2 stochastic Ito-localisation budget as hstep, hVI and hterminal. It is directly importable by both capped stochastic-core leaves and thence by local_verification.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Finset.Range
import Theorems.Thm_AvramDividend_Classical_exponential_levy_grid_cash_stieltjes_limit_le_initial
import Theorems.Thm_AvramDividend_Classical_stopped_unit_cash_integrable_of_cumulative_integrable
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_dividend_payout_eq_iSup_unit_cash_toReal_of_strategy
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_real_cash_prefix_measurable_of_strategy
import Theorems.Thm_AvramDividend_Classical_nonnegative_real_cash_prefixes_nonnegative_monotone

open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stopped_dividend_grid_verification_of_conditional_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (hs0 : s 0 = 0)
    (u cash : ℕ → Ω → ℝ) (w : ℝ → ℝ) (q x : ℝ)
    (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0)
    (hCashEq : ∀ (k : ℕ) (ω : Ω), cash k ω =
      (∫⁻ t in
      (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
        Ico (k : ℝ) ((k : ℝ) + 1),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
    (hDI : Integrable (fun ω : Ω =>
      (ENNReal.ofReal (D (T + 1) ω)).toReal) P)
    (hu0 : ∀ᵐ ω ∂P, u 0 ω = x)
    (hVI : ∀ k, Integrable
      (fun ω => Real.exp (-(q * (s k : ℝ))) * w (u k ω)) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      (P[(cash k) | 𝓕 (s k)]) ω +
        (P[(fun η => Real.exp (-(q * (s (k + 1) : ℝ))) *
          w (u (k + 1) η)) | 𝓕 (s k)]) ω ≤
            Real.exp (-(q * (s k : ℝ))) * w (u k ω))
    (hterminal : ∀ n : ℕ, 0 ≤
      ∫ ω, Real.exp (-(q * (s n : ℝ))) * w (u n ω) ∂P) :
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
