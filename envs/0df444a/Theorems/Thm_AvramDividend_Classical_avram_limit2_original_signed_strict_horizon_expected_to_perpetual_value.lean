-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_strict_horizon_expected_to_perpetual_value
-- name    : AvramDividend.Classical.avram_limit2_original_signed_strict_horizon_expected_to_perpetual_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:01:41.53246+00:00
-- url     : https://prove2.me/theorems/06b80f62-532d-4fdc-82fd-cfc74d00aa50
-- title:
--   Original perpetual dividend value from genuine signed strict stopped source budgets
-- statement:
--   For the actual admissible original strategy, assume a signed real stopped-cash-plus-terminal expected budget on each strictly positive integer horizon n+1 and AE nonnegative terminal. The admitted stopped cash finiteness proves the toReal expression equals genuine ENNReal cash. Convert each signed real budget to a genuine original stopped ENNReal expected cash+terminal bound, and use the already Proved avram_limit2_uniform_strict_horizon_cash_plus_terminal_budget_to_value (b09f3991) to pass to full dividendValue. This keeps the time-zero atom and all Iio/Iic boundaries exact and never asks terminal values to vanish. IsDividendStrategy is explicit to avoid guessing its derivation from IsAdmissible.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_expected_to_true_strict_cash_without_extra_finiteness
import Theorems.Thm_AvramDividend_Classical_avram_limit2_uniform_strict_horizon_cash_plus_terminal_budget_to_value
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_signed_strict_horizon_expected_to_perpetual_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (hDStrategy : IsDividendStrategy 𝓕 D)
    (B : ℝ≥0∞)
    (hSignedBudgets : ∀ n : ℕ, ∃ Term : Ω → ℝ,
      (∀ᵐ ω ∂P, 0 ≤ Term ω) ∧
      (∫⁻ ω, ENNReal.ofReal
        (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Iio (((n + 1 : ℕ) : ℝ)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal) + Term ω) ∂P) ≤ B) :
    dividendValue X q x D ≤ B := by sorry
