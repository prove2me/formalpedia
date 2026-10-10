-- Prove2me | Theorems.Thm_ActuarialValuation_compoundPoissonSeverityPower_zero
-- name    : ActuarialValuation.compoundPoissonSeverityPower_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:26:22.854865+00:00
-- url     : https://prove2.me/theorems/d22c7860-5957-4bbe-a869-bd18ee1035ff
-- title:
--   Exactly zero claims produce only zero aggregate loss
-- statement:
--   The zero-count claim total is the unit point mass at zero. Every positive aggregate amount has zero conditional probability when no claims have occurred, and the result requires no constraints on a potential severity distribution.
--
--   **Mathematical statement**
--
--   $$
--   f^{*0}(s)=\mathbf1_{\{s=0\}}
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib
import Definitions.Def_actuarial_compoundPoissonSeverityPower

namespace ActuarialValuation

theorem compoundPoissonSeverityPower_zero (f : ℕ → ℝ) (s : ℕ) :
  compoundPoissonSeverityPower f 0 s = (if s = 0 then 1 else 0) := by sorry

end ActuarialValuation
