-- Prove2me | Theorems.Thm_ActuarialValuation_nextStateMass_distribution
-- name    : ActuarialValuation.nextStateMass_distribution
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:12:42.129593+00:00
-- url     : https://prove2.me/theorems/06c29557-b55b-4407-8a87-375b3d678ca5
-- title:
--   Stochastic transition preserves a state probability distribution
-- statement:
--   Combines nonnegativity and unit mass for the propagated state probabilities.
--
--   **Mathematical statement**
--
--   $$
--   \mu\text{ probability},\,P\text{ stochastic}\Rightarrow\mu'\text{ probability}
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
import Definitions.Def_actuarial_isFiniteStateDistribution
import Definitions.Def_actuarial_nextStateMass
open MeasureTheory

namespace ActuarialValuation

theorem nextStateMass_distribution {S : Type*} [Fintype S] (μ : S → ℝ) (P : S → S → ℝ) (hμ : isFiniteStateDistribution μ)
  (hP : (∀ i j, 0 ≤ P i j) ∧ (∀ i, (∑ j : S, P i j) = 1))
  :
  isFiniteStateDistribution (nextStateMass μ P) := by sorry

end ActuarialValuation
