-- Prove2me | Theorems.Thm_ActuarialValuation_transitionRewardValue_linear
-- name    : ActuarialValuation.transitionRewardValue_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:10:00.378119+00:00
-- url     : https://prove2.me/theorems/860379cf-551d-4636-8ac9-b1be8b09e4d6
-- title:
--   Transition-reward valuation is linear in cashflows
-- statement:
--   Combined benefit streams can be valued by linearity of the discounted expectation.
--
--   **Mathematical statement**
--
--   $$
--   V(r_1+cr_2,V_1+cV_2)=V(r_1,V_1)+cV(r_2,V_2)
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 8 §§8.3-8.4, multiple-state transition probabilities, https://doi.org/10.1017/CBO9780511800146; Promislow (2015), Fundamentals of Actuarial Mathematics, Ch. 19 §§19.2.1-19.2.3, non-stationary finite-state Markov chains and insurance benefits; J. R. Norris (1997), Markov Chains, Ch. 1, https://doi.org/10.1017/CBO9780511810633.003.

import Mathlib
import Definitions.Def_actuarial_transitionRewardValue
open MeasureTheory

namespace ActuarialValuation

theorem transitionRewardValue_linear {S : Type*} [Fintype S] (P : S → S → ℝ) (v c : ℝ)
    (r₁ r₂ next₁ next₂ : S → ℝ) (a : S)
    :
    transitionRewardValue P v (fun b => r₁ b + c * r₂ b)
      (fun b => next₁ b + c * next₂ b) a =
      transitionRewardValue P v r₁ next₁ a +
      c * transitionRewardValue P v r₂ next₂ a := by sorry

end ActuarialValuation
