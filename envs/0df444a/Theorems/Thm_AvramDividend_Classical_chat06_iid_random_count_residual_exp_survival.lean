-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_iid_random_count_residual_exp_survival
-- name    : AvramDividend.Classical.chat06_iid_random_count_residual_exp_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:22:20.23598+00:00
-- url     : https://prove2.me/theorems/d8fea01b-848c-4ef5-ab4b-71ee44433ed7
-- title:
--   Exponential survival of the random-count-selected residual renewal wait
-- statement:
--   Let N be a measurable number of arrivals observed at a fixed clock and suppose every count-selection event N=n agrees almost surely with the precise interval S_n≤clock<S_(n+1) of an iid unit-exponential waiting-time sequence. For every nonnegative horizon t, the randomly selected residual to the next arrival, tau_N-(clock-S_N), has survival probability e^(-t). The proof uses the accepted fixed-clock count-cylinder exponential memorylessness at each n, the almost-sure count event equality and the accepted countable-partition survival-gluing theorem. This closes the random-index residual marginal law; it does not by itself prove independence from the full Poisson natural filtration or the complete marked future.
-- source:
--   Source bv_iid_random_count_residual_exp_survival_chat06_20261021.lean, 94 lines, SHA-256 2bc0f6fb841f0a41540187cd74b7d157d7fdc4ba28e21b3d80ffb01ef53392be. Remote private probe f6e79121-95ff-4a4c-947d-fa3e69697ae6 passed source elaboration to intentional sentinel with zero candidate errors at pinned Mathlib; official submission requires published target.

import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_chat06_indexed_iid_fixed_clock_count_residual
import Theorems.Thm_AvramDividend_Classical_chat06_selected_residual_survival_of_countwise_factorisation

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_iid_random_count_residual_exp_survival
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℕ) (hN : Measurable N)
    (clock t : ℝ) (ht : 0 ≤ t)
    (hTail : ∀ n (u : ℝ), 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))
    (hCount : ∀ n : ℕ,
      (fun ω : Ω => N ω = n) =ᵐ[P]
        (fun ω => (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock < ∑ i ∈ Finset.range (n + 1), τ i ω)) :
    P {ω | t < τ (N ω) ω -
      (clock - ∑ i ∈ Finset.range (N ω), τ i ω)} =
        ENNReal.ofReal (Real.exp (-t)) := by sorry
