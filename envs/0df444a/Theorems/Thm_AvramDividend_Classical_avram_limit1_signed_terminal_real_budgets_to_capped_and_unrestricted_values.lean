-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_signed_terminal_real_budgets_to_capped_and_unrestricted_values
-- name    : AvramDividend.Classical.avram_limit1_signed_terminal_real_budgets_to_capped_and_unrestricted_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:18:25.997202+00:00
-- url     : https://prove2.me/theorems/e251ba04-6cca-4ad6-b54f-47691e4b7d5d
-- title:
--   Original signed Stieltjes plus nonnegative terminal budgets imply both capped and top-cap perpetual values
-- statement:
--   For each original capped-admissible dividend strategy D at every allowed nonnegative reserve x and every positive integer closed horizon n+1, suppose the genuine expected signed discounted Stieltjes dividends plus an integrable, almost-everywhere nonnegative real terminal payoff has expected total at most w(x). The pinned Mathlib integral_nonneg_of_ae lemma makes the terminal mean nonnegative, hence the signed dividend expectation alone is bounded by w(x). The Proved original uniform signed horizon to dividendValue theorem (96f0eeb7) gives the exact unrestricted-time ENNReal reward bound on the original model. The Proved local verification supremum reducer (0d513542) gives both capped and C=top unrestricted value functions. No stopped Itô or positivity fact is inferred, and no terminal vanishing or uniform integrability is required.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_signed_terminal_real_budgets_to_capped_and_unrestricted_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hBudget : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∀ n : ℕ, ∃ Terminal : Ω → ℝ,
          Integrable Terminal P ∧
          (∀ᵐ ω ∂P, 0 ≤ Terminal ω) ∧
          ((∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
              Iic (((n + 1 : ℕ) : ℝ)),
              Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) +
            (∫ ω, Terminal ω ∂P) ≤ w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
