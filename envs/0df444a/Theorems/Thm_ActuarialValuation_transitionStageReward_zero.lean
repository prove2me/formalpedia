-- Prove2me | Theorems.Thm_ActuarialValuation_transitionStageReward_zero
-- name    : ActuarialValuation.transitionStageReward_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:13:29.567988+00:00
-- url     : https://prove2.me/theorems/18b83615-4acb-461c-ab5b-517b117a9dc2
-- title:
--   Zero transition benefits have zero stage expectation
-- statement:
--   A contract paying no benefit on any transition has zero expected one-year transition payment.
--
--   **Mathematical statement**
--
--   $$
--   b_{ij}=0\Rightarrow R^{\rm tr}=0
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
import Definitions.Def_actuarial_transitionStageReward
open MeasureTheory

namespace ActuarialValuation

theorem transitionStageReward_zero {S : Type*} [Fintype S] (μ : S → ℝ) (P : S → S → ℝ)
  :
  transitionStageReward μ P (fun _ _ => 0) = 0 := by sorry

end ActuarialValuation
