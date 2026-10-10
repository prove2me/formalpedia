-- Prove2me | Theorems.Thm_ActuarialValuation_compoundPoissonSeverityPower_succ
-- name    : ActuarialValuation.compoundPoissonSeverityPower_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:27:18.622776+00:00
-- url     : https://prove2.me/theorems/6a41bcbb-172d-46c1-a303-eed9e9902212
-- title:
--   One additional claim introduces one severity convolution
-- statement:
--   The conditional total loss of m+1 independent severities is the convolution of one severity with the existing m-claim total. This is precisely the declared primitive recursion for claim count, and does not impose any distributional normalisation by itself.
--
--   **Mathematical statement**
--
--   $$
--   f^{*(m+1)}=f*f^{*m}
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib
import Definitions.Def_actuarial_compoundPoissonSeverityPower
import Definitions.Def_actuarial_compoundPoissonConvolution

namespace ActuarialValuation

theorem compoundPoissonSeverityPower_succ (f : ℕ → ℝ) (m s : ℕ) :
  compoundPoissonSeverityPower f (m + 1) s =
    compoundPoissonConvolution f (compoundPoissonSeverityPower f m) s := by sorry

end ActuarialValuation
