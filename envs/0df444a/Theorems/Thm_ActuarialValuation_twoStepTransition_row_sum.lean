-- Prove2me | Theorems.Thm_ActuarialValuation_twoStepTransition_row_sum
-- name    : ActuarialValuation.twoStepTransition_row_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:05:50.471987+00:00
-- url     : https://prove2.me/theorems/5becd503-1898-4b98-819c-b55a7328ab62
-- title:
--   Composed transition rows sum to one
-- statement:
--   Composition preserves total transition probability by exchanging finite sums.
--
--   **Mathematical statement**
--
--   $$
--   \sum_c(PQ)_{ac}=1
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 8 §§8.3-8.4, multiple-state transition probabilities, https://doi.org/10.1017/CBO9780511800146; Promislow (2015), Fundamentals of Actuarial Mathematics, Ch. 19 §§19.2.1-19.2.3, non-stationary finite-state Markov chains and insurance benefits; J. R. Norris (1997), Markov Chains, Ch. 1, https://doi.org/10.1017/CBO9780511810633.003.

import Mathlib
import Definitions.Def_actuarial_isFiniteMarkovKernel
import Definitions.Def_actuarial_twoStepTransition
open MeasureTheory

namespace ActuarialValuation

theorem twoStepTransition_row_sum {S : Type*} [Fintype S] (P Q : S → S → ℝ)
    (hP : isFiniteMarkovKernel P) (hQ : isFiniteMarkovKernel Q) (a : S)
    :
    (∑ c : S, twoStepTransition P Q a c) = 1 := by sorry

end ActuarialValuation
