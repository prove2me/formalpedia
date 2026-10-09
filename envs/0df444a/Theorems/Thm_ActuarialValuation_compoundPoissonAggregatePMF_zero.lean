-- Prove2me | Theorems.Thm_ActuarialValuation_compoundPoissonAggregatePMF_zero
-- name    : ActuarialValuation.compoundPoissonAggregatePMF_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:30:32.279093+00:00
-- url     : https://prove2.me/theorems/c4197f6b-02f0-4057-b4df-c677931db0b0
-- title:
--   Zero aggregate loss with positive severities means zero claims
-- statement:
--   When each individual claim has strictly positive integer severity, aggregate loss zero occurs precisely for zero claims. The truncated mixture at s=0 contains exactly the zero-claim term, whose weight is the Poisson no-claim exponential.
--
--   **Mathematical statement**
--
--   $$
--   g_0=e^{-\lambda}
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib
import Definitions.Def_actuarial_compoundPoissonAggregatePMF
import Definitions.Def_actuarial_compoundPoissonCountWeight
import Definitions.Def_actuarial_compoundPoissonSeverityPower

namespace ActuarialValuation

theorem compoundPoissonAggregatePMF_zero (rate : ℝ) (f : ℕ → ℝ)
  (hzero : f 0 = 0) :
  compoundPoissonAggregatePMF rate f 0 = Real.exp (-rate) := by sorry

end ActuarialValuation
