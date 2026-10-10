-- Prove2me | Theorems.Thm_ActuarialValuation_retainedExcessLoss_mono_limit
-- name    : ActuarialValuation.retainedExcessLoss_mono_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T06:18:36.783641+00:00
-- url     : https://prove2.me/theorems/0c6c0f02-444a-4139-89f2-a2a99f634c68
-- title:
--   Retained loss rises with retention
-- statement:
--   Increasing the retention limit does not decrease the insurer's retained loss.
--
--   **Mathematical statement**
--
--   $$
--   a\le b\implies r(z,a)\le r(z,b)
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
import Definitions.Def_actuarial_retainedExcessLoss
open MeasureTheory

namespace ActuarialValuation

theorem retainedExcessLoss_mono_limit (z a b : ℝ) (hab : a ≤ b)
  :
  retainedExcessLoss z a ≤ retainedExcessLoss z b := by sorry

end ActuarialValuation
