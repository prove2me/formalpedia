-- Prove2me | Theorems.Thm_ActuarialValuation_reinsuranceFiniteActionBellman_fundamental
-- name    : ActuarialValuation.reinsuranceFiniteActionBellman_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T06:23:23.358197+00:00
-- url     : https://prove2.me/theorems/5e81bc66-93a3-4f33-bbf7-00302a4aa45f
-- title:
--   Finite-action reinsurance Bellman optimality capstone
-- statement:
--   For each finite-state starting point, the Bellman value bounds all actions and some admissible action attains that optimal value.
--
--   **Mathematical statement**
--
--   $$
--   \forall a,\ Q(s,a)\le TV(s),\qquad \exists a^\star\in A:\ Q(s,a^\star)=TV(s)
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
import Definitions.Def_actuarial_finiteActionBellmanValue
open MeasureTheory

namespace ActuarialValuation

theorem reinsuranceFiniteActionBellman_fundamental {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (next : S → ℝ) (s : S)
  :
  (∀ a : A, reward s a +
       v * (∑ t : S, P s a t * next t) ≤
          finiteActionBellmanValue P reward v next s)
  ∧ (∃ a : A, finiteActionBellmanValue P reward v next s =
       reward s a + v * (∑ t : S, P s a t * next t)) := by sorry

end ActuarialValuation
