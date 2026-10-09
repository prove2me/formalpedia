-- Prove2me | Theorems.Thm_ActuarialValuation_transitionRewardValue_zero_discount
-- name    : ActuarialValuation.transitionRewardValue_zero_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:08:15.257052+00:00
-- url     : https://prove2.me/theorems/104bce00-db62-4043-b06f-bcd9fcd1209b
-- title:
--   Zero discount produces zero one-step value
-- statement:
--   If the next-year cashflows are discounted by zero, the one-step value is zero.
--
--   **Mathematical statement**
--
--   $$
--   v=0\Longrightarrow V(a)=0
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 8 §§8.3-8.4, multiple-state transition probabilities, https://doi.org/10.1017/CBO9780511800146; Promislow (2015), Fundamentals of Actuarial Mathematics, Ch. 19 §§19.2.1-19.2.3, non-stationary finite-state Markov chains and insurance benefits; J. R. Norris (1997), Markov Chains, Ch. 1, https://doi.org/10.1017/CBO9780511810633.003.

import Mathlib
import Definitions.Def_actuarial_transitionRewardValue
open MeasureTheory

namespace ActuarialValuation

theorem transitionRewardValue_zero_discount {S : Type*} [Fintype S] (P : S → S → ℝ) (r next : S → ℝ) (a : S)
    :
    transitionRewardValue P 0 r next a = 0 := by sorry

end ActuarialValuation
