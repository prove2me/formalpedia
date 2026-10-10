-- Prove2me | Theorems.Thm_ActuarialValuation_pvBenefit_zero
-- name    : ActuarialValuation.pvBenefit_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:15:26.50445+00:00
-- url     : https://prove2.me/theorems/d563fc22-ef6a-44fa-970a-7901e35a1d89
-- title:
--   Finite random present values of insurance benefits and premium streams: pvBenefit_zero
-- statement:
--   A zero sum insured yields no discounted benefit in any scenario.
--
--   Mathematical relation:
--
--   $$
--   pvBenefit\_zero
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvBenefit

namespace ActuarialValuation

theorem pvBenefit_zero {n : ℕ} (discount : Fin n → ℝ) (i : Fin n) : pvBenefit (fun _ => 0) discount i = 0 := by sorry

end ActuarialValuation
