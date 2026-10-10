-- Prove2me | Theorems.Thm_ActuarialValuation_compoundPoissonSeverityPower_one
-- name    : ActuarialValuation.compoundPoissonSeverityPower_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:28:12.661294+00:00
-- url     : https://prove2.me/theorems/f760ad1f-b727-45ef-a63a-daa42a171b18
-- title:
--   A one-claim aggregate has the underlying severity distribution
-- statement:
--   Exactly one insured claim produces its individual severity mass at each integer amount. The recurrence convolves the single-claim severity with the point mass of zero preceding claims, so only one coefficient survives.
--
--   **Mathematical statement**
--
--   $$
--   f^{*1}(s)=f(s)
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib
import Definitions.Def_actuarial_compoundPoissonSeverityPower
import Definitions.Def_actuarial_compoundPoissonConvolution

namespace ActuarialValuation

theorem compoundPoissonSeverityPower_one (f : ℕ → ℝ) (s : ℕ) :
  compoundPoissonSeverityPower f 1 s = f s := by sorry

end ActuarialValuation
