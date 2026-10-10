-- Prove2me | Theorems.Thm_ActuarialValuation_retainedExcessLoss_zero_limit
-- name    : ActuarialValuation.retainedExcessLoss_zero_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T06:16:08.440449+00:00
-- url     : https://prove2.me/theorems/b7999665-7fa2-4860-9914-5a039a2638a7
-- title:
--   Zero retention transfers all nonnegative claims
-- statement:
--   If the retention is zero and gross claim nonnegative the insurer retains no claim.
--
--   **Mathematical statement**
--
--   $$
--   a=0\implies r(z,0)=0
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
import Definitions.Def_actuarial_retainedExcessLoss
open MeasureTheory

namespace ActuarialValuation

theorem retainedExcessLoss_zero_limit (z : ℝ) (hz : 0 ≤ z)
  :
  retainedExcessLoss z 0 = 0 := by sorry

end ActuarialValuation
