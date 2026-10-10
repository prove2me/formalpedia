-- Prove2me | Theorems.Thm_ActuarialValuation_pvExpected_const
-- name    : ActuarialValuation.pvExpected_const
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:17:49.517505+00:00
-- url     : https://prove2.me/theorems/c604cf08-c845-4eef-9a23-e5153c0e01f2
-- title:
--   Equivalence premiums and loss variance: pvExpected_const
-- statement:
--   The expectation of a deterministic loss equals that loss under probability normalisation.
--
--   Mathematical relation:
--
--   $$
--   pvExpected\_const
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpected

namespace ActuarialValuation

theorem pvExpected_const {n : ℕ} (p : Fin n → ℝ) (a : ℝ) (hp : (∑ i : Fin n, p i) = 1) : pvExpected p (fun _ => a) = a := by sorry

end ActuarialValuation
