-- Prove2me | Theorems.Thm_ActuarialValuation_compoundPoissonCountWeight_zero
-- name    : ActuarialValuation.compoundPoissonCountWeight_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:29:17.473747+00:00
-- url     : https://prove2.me/theorems/1cd51cbb-35e1-45f7-b40e-822250dd41c0
-- title:
--   Zero-claim Poisson weight equals exponential no-claim probability
-- statement:
--   For claim count zero, the rate power and factorial both equal one. Consequently the Poisson count weight simplifies to the exponential of the negative frequency rate.
--
--   **Mathematical statement**
--
--   $$
--   p_0=e^{-\lambda}
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib
import Definitions.Def_actuarial_compoundPoissonCountWeight

namespace ActuarialValuation

theorem compoundPoissonCountWeight_zero (rate : ℝ) :
  compoundPoissonCountWeight rate 0 = Real.exp (-rate) := by sorry

end ActuarialValuation
