-- Prove2me | Theorems.Thm_ActuarialValuation_finiteHorizonPolicyValue_zero
-- name    : ActuarialValuation.finiteHorizonPolicyValue_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T07:13:46.871533+00:00
-- url     : https://prove2.me/theorems/82dada8b-afc7-4e91-8c3d-7bfd2fe5b492
-- title:
--   Zero-decision policy value is terminal benefit
-- statement:
--   At zero remaining horizon, no policy action is taken and terminal benefit is paid.
--
--   **Mathematical statement**
--
--   $$
--   V^\pi_0(s)=h(s)
--   $$
-- source:
--   Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman optimality and finite-state/action deterministic Markov optimal policies, https://doi.org/10.1002/9780470316887.ch4; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048, motivational context only, not continuous-time verification

import Mathlib
import Definitions.Def_actuarial_finiteHorizonPolicyValue
open MeasureTheory

namespace ActuarialValuation

theorem finiteHorizonPolicyValue_zero {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] (P : S → A → S → ℝ) (reward : S → A → ℝ)
  (v : ℝ) (terminal : S → ℝ) (policy : ℕ → S → A) (s : S)
  :
  finiteHorizonPolicyValue P reward v terminal policy 0 s = terminal s := by sorry

end ActuarialValuation
