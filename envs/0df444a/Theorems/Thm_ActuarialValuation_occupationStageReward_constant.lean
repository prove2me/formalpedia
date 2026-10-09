-- Prove2me | Theorems.Thm_ActuarialValuation_occupationStageReward_constant
-- name    : ActuarialValuation.occupationStageReward_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:15:06.694549+00:00
-- url     : https://prove2.me/theorems/7324a60c-bbd9-4c53-b204-d3dc4212a5f0
-- title:
--   Certain constant occupation payment
-- statement:
--   A constant amount payable in every state has expected value equal to that amount.
--
--   **Mathematical statement**
--
--   $$
--   c_i=a\Rightarrow R^{\rm occ}=a
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
import Definitions.Def_actuarial_occupationStageReward
open MeasureTheory

namespace ActuarialValuation

theorem occupationStageReward_constant {S : Type*} [Fintype S] (μ : S → ℝ) (hμ : (∑ i : S, μ i) = 1) (a : ℝ)
  :
  occupationStageReward μ (fun _ => a) = a := by sorry

end ActuarialValuation
