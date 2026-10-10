-- Prove2me | Theorems.Thm_ActuarialValuation_compoundPoissonAggregatePMF_rate_zero
-- name    : ActuarialValuation.compoundPoissonAggregatePMF_rate_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:31:29.556109+00:00
-- url     : https://prove2.me/theorems/f2fd1224-1be0-4b59-9204-78871ab14240
-- title:
--   No claim arrivals imply a point mass at zero loss
-- statement:
--   With Poisson frequency zero, only the zero-count term has positive weight. All positive claim-count terms contain a strictly positive power of zero and vanish; the remaining zero-claim severity convolution is a point mass at aggregate loss zero.
--
--   **Mathematical statement**
--
--   $$
--   g_s(0)=\mathbf1_{\{s=0\}}
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib
import Definitions.Def_actuarial_compoundPoissonAggregatePMF
import Definitions.Def_actuarial_compoundPoissonCountWeight
import Definitions.Def_actuarial_compoundPoissonSeverityPower

namespace ActuarialValuation

theorem compoundPoissonAggregatePMF_rate_zero (f : ℕ → ℝ) (s : ℕ) :
  compoundPoissonAggregatePMF 0 f s = (if s = 0 then 1 else 0) := by sorry

end ActuarialValuation
