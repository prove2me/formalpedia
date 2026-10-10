-- Prove2me | Theorems.Thm_ActuarialValuation_pvExpected_add
-- name    : ActuarialValuation.pvExpected_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:18:05.091981+00:00
-- url     : https://prove2.me/theorems/5ea1f242-2aff-4f5d-a469-eecbd941b1d7
-- title:
--   Equivalence premiums and loss variance: pvExpected_add
-- statement:
--   Expected loss is additive across two payoffs evaluated on the same random insured state.
--
--   Mathematical relation:
--
--   $$
--   pvExpected\_add
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpected

namespace ActuarialValuation

theorem pvExpected_add {n : ℕ} (p a b : Fin n → ℝ) : pvExpected p (fun i => a i + b i) = pvExpected p a + pvExpected p b := by sorry

end ActuarialValuation
