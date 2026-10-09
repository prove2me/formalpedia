-- Prove2me | Theorems.Thm_ActuarialValuation_occupationStageReward_zero
-- name    : ActuarialValuation.occupationStageReward_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:14:29.863735+00:00
-- url     : https://prove2.me/theorems/031855a0-93b5-42a8-9891-b7bc16001390
-- title:
--   Zero state-occupation payments have zero stage expectation
-- statement:
--   If no state has a payment at the beginning of the year, expected occupation benefit is zero.
--
--   **Mathematical statement**
--
--   $$
--   c_i=0\Rightarrow R^{\rm occ}=0
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
import Definitions.Def_actuarial_occupationStageReward
open MeasureTheory

namespace ActuarialValuation

theorem occupationStageReward_zero {S : Type*} [Fintype S] (μ : S → ℝ)
  :
  occupationStageReward μ (fun _ => 0) = 0 := by sorry

end ActuarialValuation
