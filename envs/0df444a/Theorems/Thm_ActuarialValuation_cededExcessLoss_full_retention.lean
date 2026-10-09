-- Prove2me | Theorems.Thm_ActuarialValuation_cededExcessLoss_full_retention
-- name    : ActuarialValuation.cededExcessLoss_full_retention
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T06:16:43.833153+00:00
-- url     : https://prove2.me/theorems/c8a4cb13-1fed-4505-afaa-ee2c17c956c9
-- title:
--   Retention above claim cedes nothing
-- statement:
--   Where the claim lies below the retention limit there is no reinsurance recovery.
--
--   **Mathematical statement**
--
--   $$
--   z\le a\implies c(z,a)=0
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
import Definitions.Def_actuarial_cededExcessLoss
open MeasureTheory

namespace ActuarialValuation

theorem cededExcessLoss_full_retention (z a : ℝ) (hza : z ≤ a)
  :
  cededExcessLoss z a = 0 := by sorry

end ActuarialValuation
