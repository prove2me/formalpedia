-- Prove2me | Theorems.Thm_ActuarialValuation_transitionRewardValue_zero_cashflows
-- name    : ActuarialValuation.transitionRewardValue_zero_cashflows
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:08:45.059729+00:00
-- url     : https://prove2.me/theorems/33d69417-f04d-4899-aea5-fc458adb710d
-- title:
--   Zero rewards and continuation give zero value
-- statement:
--   A transition model with no future payment has zero value.
--
--   **Mathematical statement**
--
--   $$
--   r=0,\ V_{\rm next}=0\Longrightarrow V=0
--   $$
-- source:
--   Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Ch. 8 §§8.3-8.4, multiple-state transition probabilities, https://doi.org/10.1017/CBO9780511800146; Promislow (2015), Fundamentals of Actuarial Mathematics, Ch. 19 §§19.2.1-19.2.3, non-stationary finite-state Markov chains and insurance benefits; J. R. Norris (1997), Markov Chains, Ch. 1, https://doi.org/10.1017/CBO9780511810633.003.

import Mathlib
import Definitions.Def_actuarial_transitionRewardValue
open MeasureTheory

namespace ActuarialValuation

theorem transitionRewardValue_zero_cashflows {S : Type*} [Fintype S] (P : S → S → ℝ) (v : ℝ) (a : S)
    :
    transitionRewardValue P v (fun _ => 0) (fun _ => 0) a = 0 := by sorry

end ActuarialValuation
