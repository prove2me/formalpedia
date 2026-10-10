-- Prove2me | Theorems.Thm_ActuarialValuation_compoundPoissonCountWeight_ratio
-- name    : ActuarialValuation.compoundPoissonCountWeight_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:29:43.477689+00:00
-- url     : https://prove2.me/theorems/7213b9aa-b2af-482a-a11b-b1626500bfa0
-- title:
--   Adjacent Poisson count masses obey the factorial recursion
-- statement:
--   The consecutive Poisson mass ratio is λ/(m+1). Multiplication by the next count cancels the extra factorial term, furnishing the counting-distribution recursion that underlies Panjer's aggregate-loss coefficient identity.
--
--   **Mathematical statement**
--
--   $$
--   (m+1)p_{m+1}=\lambda p_m
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib
import Definitions.Def_actuarial_compoundPoissonCountWeight

namespace ActuarialValuation

theorem compoundPoissonCountWeight_ratio (rate : ℝ) (m : ℕ) :
  (m + 1 : ℝ) * compoundPoissonCountWeight rate (m + 1) =
    rate * compoundPoissonCountWeight rate m := by sorry

end ActuarialValuation
