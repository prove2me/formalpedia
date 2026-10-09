-- Prove2me | Theorems.Thm_ActuarialValuation_transitionRewardValue_constant
-- name    : ActuarialValuation.transitionRewardValue_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:09:25.547555+00:00
-- url     : https://prove2.me/theorems/8e1bd93d-5355-4908-9efa-c68a91b4fd49
-- title:
--   A certain next-year cashflow is discounted once
-- statement:
--   A reward of c in every next state has value v times c because transition probabilities sum to one.
--
--   **Mathematical statement**
--
--   $$
--   r_b=c\Longrightarrow V(a)=vc
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 8 §§8.3-8.4, multiple-state transition probabilities, https://doi.org/10.1017/CBO9780511800146; Promislow (2015), Fundamentals of Actuarial Mathematics, Ch. 19 §§19.2.1-19.2.3, non-stationary finite-state Markov chains and insurance benefits; J. R. Norris (1997), Markov Chains, Ch. 1, https://doi.org/10.1017/CBO9780511810633.003.

import Mathlib
import Definitions.Def_actuarial_isFiniteMarkovKernel
import Definitions.Def_actuarial_transitionRewardValue
open MeasureTheory

namespace ActuarialValuation

theorem transitionRewardValue_constant {S : Type*} [Fintype S] (P : S → S → ℝ) (hP : isFiniteMarkovKernel P) (v c : ℝ) (a : S)
    :
    transitionRewardValue P v (fun _ => c) (fun _ => 0) a = v * c := by sorry

end ActuarialValuation
