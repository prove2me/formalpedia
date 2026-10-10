-- Prove2me | Theorems.Thm_ActuarialValuation_retainedExcessLoss_le_limit
-- name    : ActuarialValuation.retainedExcessLoss_le_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T06:09:28.309977+00:00
-- url     : https://prove2.me/theorems/37ed2102-3ac3-49c7-8ff8-f422468ae815
-- title:
--   Retained loss does not exceed retention limit
-- statement:
--   Maximum exposure under excess-of-loss is capped by the retention.
--
--   **Mathematical statement**
--
--   $$
--   r(z,a)\le a
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
import Definitions.Def_actuarial_retainedExcessLoss
open MeasureTheory

namespace ActuarialValuation

theorem retainedExcessLoss_le_limit (z a : ℝ)
  :
  retainedExcessLoss z a ≤ a := by sorry

end ActuarialValuation
