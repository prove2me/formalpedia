-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_uniform_closed_cash_plus_terminal_to_capped_and_top_values
-- name    : AvramDividend.Classical.avram_limit2_uniform_closed_cash_plus_terminal_to_capped_and_top_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:27:54.305187+00:00
-- url     : https://prove2.me/theorems/9c4951a4-1c2b-4486-a84f-d00368e3c19d
-- title:
--   Original closed-horizon dividend cash plus nonnegative terminal budgets imply capped and unrestricted perpetual values
-- statement:
--   For every genuine capped original admissible dividend strategy and nonnegative reserve in cap, suppose each closed finite horizon Iic(n) expected discounted Stieltjes payout plus an arbitrary ENNReal nonnegative terminal has total expected mass bounded by ENNReal.ofReal(w x). The Proved original dividendValue_eq_iSup_truncated exhausts perpetual dividends by the exact closed Iic(n) expectations. Mathlib lintegral_mono makes the cash smaller than cash plus terminal, and iSup_le bounds the actual perpetual strategy dividendValue. The Proved source local_verification_from_uniform_strategy_bound converts these uniform per-strategy bounds into capped valueFunctionLe and at C=top unrestricted valueFunction upper bounds. This preserves time-zero and right-horizon atoms and assumes no terminal vanishing, equality-in-law, stochastic martingales, or q sign restriction.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_uniform_closed_cash_plus_terminal_to_capped_and_top_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hBudget : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
          (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Iic (n : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤
            ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
