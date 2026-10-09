-- Prove2me | Theorems.Thm_ActuarialValuation_compoundPoissonAggregatePMF_panjer
-- name    : ActuarialValuation.compoundPoissonAggregatePMF_panjer
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:34:13.395273+00:00
-- url     : https://prove2.me/theorems/8ea23245-911b-4ff2-89d9-68cd09b2dc33
-- title:
--   Compound Poisson coefficients satisfy Panjer's recursion
-- statement:
--   For positive integer severity the compound Poisson coefficient mixture is equal to a one-step recursion on lower aggregate-loss coefficients. The algebra uses the Poisson count factorial relation and the convolution-power identities, and exactly avoids an infinite numerical count sum for each requested s.
--
--   **Mathematical statement**
--
--   $$
--   g_{s+1}=\frac{\lambda}{s+1}\sum_{j=1}^{s+1}jf_jg_{s+1-j}
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib
import Definitions.Def_actuarial_compoundPoissonAggregatePMF
import Definitions.Def_actuarial_compoundPoissonPanjerStep
import Definitions.Def_actuarial_compoundPoissonSeverityPower

namespace ActuarialValuation

theorem compoundPoissonAggregatePMF_panjer
  (rate : ℝ) (f : ℕ → ℝ) (s : ℕ)
  (hf0 : f 0 = 0) :
  compoundPoissonAggregatePMF rate f (s + 1) =
    compoundPoissonPanjerStep rate f
      (compoundPoissonAggregatePMF rate f) (s + 1) := by sorry

end ActuarialValuation
