-- Prove2me | Theorems.Thm_ActuarialValuation_finiteState_valuation_fundamental
-- name    : ActuarialValuation.finiteState_valuation_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:11:54.295765+00:00
-- url     : https://prove2.me/theorems/cdcbb0c5-5e97-44c5-a167-de72d1b9de0f
-- title:
--   Finite-state Markov transition and valuation capstone
-- statement:
--   Combines preservation of stochastic kernels, associative composition and the discounted two-step reward identity.
--
--   **Mathematical statement**
--
--   $$
--   \sum_c(PQ)_{ac}=1,\qquad (PQ)R=P(QR),\qquad V_0=v^2\sum_c(PQ)_{ac}r_c
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 8 §§8.3-8.4, multiple-state transition probabilities, https://doi.org/10.1017/CBO9780511800146; Promislow (2015), Fundamentals of Actuarial Mathematics, Ch. 19 §§19.2.1-19.2.3, non-stationary finite-state Markov chains and insurance benefits; J. R. Norris (1997), Markov Chains, Ch. 1, https://doi.org/10.1017/CBO9780511810633.003.

import Mathlib
import Definitions.Def_actuarial_isFiniteMarkovKernel
import Definitions.Def_actuarial_twoStepTransition
import Definitions.Def_actuarial_transitionRewardValue
open MeasureTheory

namespace ActuarialValuation

theorem finiteState_valuation_fundamental {S : Type*} [Fintype S] (P Q R : S → S → ℝ) (hP : isFiniteMarkovKernel P)
    (hQ : isFiniteMarkovKernel Q) (v : ℝ) (r : S → ℝ) (a d : S)
    :
    (isFiniteMarkovKernel (twoStepTransition P Q))
    ∧ (twoStepTransition (twoStepTransition P Q) R a d =
         twoStepTransition P (twoStepTransition Q R) a d)
    ∧ (transitionRewardValue P v (fun _ => 0)
         (fun b => transitionRewardValue Q v r (fun _ => 0) b) a =
         v ^ 2 * (∑ c : S, twoStepTransition P Q a c * r c)) := by sorry

end ActuarialValuation
