-- Prove2me | Theorems.Thm_ActuarialValuation_crSpread_symmetry
-- name    : ActuarialValuation.crSpread_symmetry
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:38:12.651981+00:00
-- url     : https://prove2.me/theorems/b064f972-e120-4ff3-92bf-f4c03f345cbd
-- title:
--   Coherent worst-case actuarial premium and portfolio: crSpread_symmetry
-- statement:
--   The uncertainty spread is symmetric in the two probability scenarios.
--
--   Mathematical relation:
--
--   $$
--   crSpread\_symmetry
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crAmbiguitySpread

namespace ActuarialValuation

theorem crSpread_symmetry {n : ℕ} (p q X : Fin n→ℝ) : crAmbiguitySpread p q X = crAmbiguitySpread q p X := by sorry

end ActuarialValuation
