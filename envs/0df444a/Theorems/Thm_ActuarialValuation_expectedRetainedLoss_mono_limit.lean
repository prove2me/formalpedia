-- Prove2me | Theorems.Thm_ActuarialValuation_expectedRetainedLoss_mono_limit
-- name    : ActuarialValuation.expectedRetainedLoss_mono_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T06:19:49.536264+00:00
-- url     : https://prove2.me/theorems/bc7046d0-d48d-4831-9452-2684bafa806c
-- title:
--   Expected retained loss rises with retention
-- statement:
--   With nonnegative scenario weights a higher retention cannot reduce expected retained claims.
--
--   **Mathematical statement**
--
--   $$
--   a\le b\implies\mathbb E[r(Z,a)]\le\mathbb E[r(Z,b)]
--   $$
-- source:
--   Brachetta and Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, Risks 7(2) 48, DOI https://doi.org/10.3390/risks7020048, §2 retained loss min(z,alpha), §3 HJB optimisation; Puterman (1994), Markov Decision Processes: Discrete Stochastic Dynamic Programming, Chapter 4 finite-horizon Bellman/backward induction, https://doi.org/10.1002/9780470316887.ch4

import Mathlib
import Definitions.Def_actuarial_expectedRetainedLoss
open MeasureTheory

namespace ActuarialValuation

theorem expectedRetainedLoss_mono_limit {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (a b : ℝ)
  (hw : ∀ ω, 0 ≤ w ω) (hab : a ≤ b)
  :
  expectedRetainedLoss w z a ≤ expectedRetainedLoss w z b := by sorry

end ActuarialValuation
