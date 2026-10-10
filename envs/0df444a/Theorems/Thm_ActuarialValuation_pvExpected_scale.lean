-- Prove2me | Theorems.Thm_ActuarialValuation_pvExpected_scale
-- name    : ActuarialValuation.pvExpected_scale
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:18:18.050205+00:00
-- url     : https://prove2.me/theorems/0f50ca0a-eff2-4717-962e-dbfb9a9e5629
-- title:
--   Equivalence premiums and loss variance: pvExpected_scale
-- statement:
--   Expectation is linear in the monetary scale of loss.
--
--   Mathematical relation:
--
--   $$
--   pvExpected\_scale
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpected

namespace ActuarialValuation

theorem pvExpected_scale {n : ℕ} (p a : Fin n → ℝ) (c : ℝ) : pvExpected p (fun i => c * a i) = c * pvExpected p a := by sorry

end ActuarialValuation
