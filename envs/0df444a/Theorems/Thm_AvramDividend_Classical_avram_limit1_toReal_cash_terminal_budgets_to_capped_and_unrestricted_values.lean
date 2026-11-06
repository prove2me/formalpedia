-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_toReal_cash_terminal_budgets_to_capped_and_unrestricted_values
-- name    : AvramDividend.Classical.avram_limit1_toReal_cash_terminal_budgets_to_capped_and_unrestricted_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:19:53.930445+00:00
-- url     : https://prove2.me/theorems/35680511-0bda-4332-9a05-006f34495bbe
-- title:
--   Original stopped ENNReal.toReal signed cash and nonnegative terminal budgets control capped and unrestricted values
-- statement:
--   For each original capped-admissible strategy and all closed positive integer horizons, suppose that the real expectation of the exact canonical ENNReal Stieltjes cash fibre converted with toReal, plus the real expectation of an integrable a.e. nonnegative terminal payoff, is bounded by w(x). The Proved original real-horizon toReal-to-signed-Stieltjes mean equality (f9800645) identifies exactly that cash expectation with the original signed real Stieltjes mean. Mathlib integral_nonneg_of_ae makes the terminal expectation nonnegative. The Proved original uniform signed-horizon budget-to-dividendValue theorem (96f0eeb7) and local strategy supremum reducer (0d513542) yield both capped and C=top unrestricted value bounds. This is an exact shape for P3 signed stopped HJB output; the stochastic bound and terminal positivity remain explicit premises. It requires no terminal vanishing, equality in law, or new stochastic martingale proof.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_ennreal_fibre_toReal_mean_eq_signed_stieltjes_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_strategy_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_toReal_cash_terminal_budgets_to_capped_and_unrestricted_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hBudget : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∀ n : ℕ, ∃ Terminal : Ω → ℝ,
          Integrable Terminal P ∧
          (∀ᵐ ω ∂P, 0 ≤ Terminal ω) ∧
          ((∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Iic (((n + 1 : ℕ) : ℝ)),
              ENNReal.ofReal (Real.exp (-(q * t)))
                ∂(dividendMeasure D ω)).toReal ∂P) +
            (∫ ω, Terminal ω ∂P) ≤ w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
