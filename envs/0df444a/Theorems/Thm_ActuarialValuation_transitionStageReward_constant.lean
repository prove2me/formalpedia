-- Prove2me | Theorems.Thm_ActuarialValuation_transitionStageReward_constant
-- name    : ActuarialValuation.transitionStageReward_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:16:41.202694+00:00
-- url     : https://prove2.me/theorems/4092b01e-6613-450c-a60d-04c313691500
-- title:
--   Constant transition benefit equals its face amount
-- statement:
--   An amount paid on every one-year transition has unit total transition probability.
--
--   **Mathematical statement**
--
--   $$
--   b_{ij}=a\Rightarrow R^{\rm tr}=a
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
import Definitions.Def_actuarial_transitionStageReward
open MeasureTheory

namespace ActuarialValuation

theorem transitionStageReward_constant {S : Type*} [Fintype S] (μ : S → ℝ) (P : S → S → ℝ) (hμ : (∑ i : S, μ i) = 1)
  (hP : ∀ i, (∑ j : S, P i j) = 1) (a : ℝ)
  :
  transitionStageReward μ P (fun _ _ => a) = a := by sorry

end ActuarialValuation
