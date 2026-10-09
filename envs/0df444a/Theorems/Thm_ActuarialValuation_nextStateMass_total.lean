-- Prove2me | Theorems.Thm_ActuarialValuation_nextStateMass_total
-- name    : ActuarialValuation.nextStateMass_total
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:12:15.61056+00:00
-- url     : https://prove2.me/theorems/8647f1c7-0abe-42fb-98e2-19a5f37e012d
-- title:
--   Propagation preserves total mass
-- statement:
--   Summing over arrival states and then initial states shows that row-stochastic transition preserves mass one.
--
--   **Mathematical statement**
--
--   $$
--   \sum_j\mu'_j=1
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
import Definitions.Def_actuarial_nextStateMass
open MeasureTheory

namespace ActuarialValuation

theorem nextStateMass_total {S : Type*} [Fintype S] (μ : S → ℝ) (P : S → S → ℝ) (hμ : (∑ i : S, μ i) = 1) (hP : ∀ i, (∑ j : S, P i j) = 1)
  :
  (∑ j : S, nextStateMass μ P j) = 1 := by sorry

end ActuarialValuation
