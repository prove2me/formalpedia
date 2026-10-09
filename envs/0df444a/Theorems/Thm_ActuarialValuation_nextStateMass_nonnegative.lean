-- Prove2me | Theorems.Thm_ActuarialValuation_nextStateMass_nonnegative
-- name    : ActuarialValuation.nextStateMass_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:11:39.447772+00:00
-- url     : https://prove2.me/theorems/b65712ff-c3b2-4fc4-84dc-8f69ebfd9aeb
-- title:
--   Distribution propagation preserves nonnegative masses
-- statement:
--   All terms in the propagated destination-state mass are nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   \mu,P\ge0\Rightarrow\mu'_j\ge0
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
import Definitions.Def_actuarial_nextStateMass
open MeasureTheory

namespace ActuarialValuation

theorem nextStateMass_nonnegative {S : Type*} [Fintype S] (μ : S → ℝ) (P : S → S → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hP : ∀ i j, 0 ≤ P i j) (j : S)
  :
  0 ≤ nextStateMass μ P j := by sorry

end ActuarialValuation
