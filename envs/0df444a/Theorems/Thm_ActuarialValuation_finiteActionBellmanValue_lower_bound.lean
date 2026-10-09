-- Prove2me | Theorems.Thm_ActuarialValuation_finiteActionBellmanValue_lower_bound
-- name    : ActuarialValuation.finiteActionBellmanValue_lower_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T06:22:50.729295+00:00
-- url     : https://prove2.me/theorems/6df02d6c-e303-47c1-b48c-d8620e75ae48
-- title:
--   Bellman value dominates every admissible action
-- statement:
--   The optimal finite-action value is at least the value of any particular admissible retention or control action.
--
--   **Mathematical statement**
--
--   $$
--   Q(s,a)\le (TV)(s)
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
import Definitions.Def_actuarial_finiteActionBellmanValue
open MeasureTheory

namespace ActuarialValuation

theorem finiteActionBellmanValue_lower_bound {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (next : S → ℝ) (s : S) (a : A)
  :
  reward s a + v * (∑ t : S, P s a t * next t) ≤
    finiteActionBellmanValue P reward v next s := by sorry

end ActuarialValuation
