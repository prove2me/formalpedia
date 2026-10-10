-- Prove2me | Theorems.Thm_ActuarialValuation_retentionOneStepCost_eq
-- name    : ActuarialValuation.retentionOneStepCost_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T06:20:43.321564+00:00
-- url     : https://prove2.me/theorems/4461bdd2-5840-4153-bcc6-22507865f5c9
-- title:
--   Reinsurance retention stage cost separates
-- statement:
--   The order of adding expected claim cost and reinsurance premium is immaterial.
--
--   **Mathematical statement**
--
--   $$
--   C(a)=q(a)+\mathbb E[r(Z,a)]
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
import Definitions.Def_actuarial_expectedRetainedLoss
import Definitions.Def_actuarial_retentionOneStepCost
open MeasureTheory

namespace ActuarialValuation

theorem retentionOneStepCost_eq {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (q : ℝ → ℝ) (a : ℝ)
  :
  retentionOneStepCost w z q a = q a + expectedRetainedLoss w z a := by sorry

end ActuarialValuation
