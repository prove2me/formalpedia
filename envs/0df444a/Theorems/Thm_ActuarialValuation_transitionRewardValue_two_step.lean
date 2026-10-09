-- Prove2me | Theorems.Thm_ActuarialValuation_transitionRewardValue_two_step
-- name    : ActuarialValuation.transitionRewardValue_two_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:11:15.302263+00:00
-- url     : https://prove2.me/theorems/cbde5817-3681-46e1-82f2-b4e61eaa0182
-- title:
--   A two-step discount-value identity
-- statement:
--   If all rewards arise at the second year end, transition composition and valuation agree with two-year discounting.
--
--   **Mathematical statement**
--
--   $$
--   V_0=v^2\sum_c(PQ)_{ac}r_c
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 8 §§8.3-8.4, multiple-state transition probabilities, https://doi.org/10.1017/CBO9780511800146; Promislow (2015), Fundamentals of Actuarial Mathematics, Ch. 19 §§19.2.1-19.2.3, non-stationary finite-state Markov chains and insurance benefits; J. R. Norris (1997), Markov Chains, Ch. 1, https://doi.org/10.1017/CBO9780511810633.003.

import Mathlib
import Definitions.Def_actuarial_twoStepTransition
import Definitions.Def_actuarial_transitionRewardValue
open MeasureTheory

namespace ActuarialValuation

theorem transitionRewardValue_two_step {S : Type*} [Fintype S] (P Q : S → S → ℝ) (v : ℝ)
    (r : S → ℝ) (a : S)
    :
    transitionRewardValue P v (fun _ => 0)
       (fun b => transitionRewardValue Q v r (fun _ => 0) b) a =
      v ^ 2 * (∑ c : S, twoStepTransition P Q a c * r c) := by sorry

end ActuarialValuation
