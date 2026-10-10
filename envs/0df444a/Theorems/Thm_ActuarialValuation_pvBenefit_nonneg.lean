-- Prove2me | Theorems.Thm_ActuarialValuation_pvBenefit_nonneg
-- name    : ActuarialValuation.pvBenefit_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:15:37.176674+00:00
-- url     : https://prove2.me/theorems/77a5b7b7-5bd8-479e-bb59-fc2137af44a1
-- title:
--   Finite random present values of insurance benefits and premium streams: pvBenefit_nonneg
-- statement:
--   A nonnegative insurance sum insured discounted by a nonnegative factor produces nonnegative random present value.
--
--   Mathematical relation:
--
--   $$
--   pvBenefit\_nonneg
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvBenefit

namespace ActuarialValuation

theorem pvBenefit_nonneg {n : ℕ} (benefit discount : Fin n → ℝ) (i : Fin n) (hb : 0 ≤ benefit i) (hd : 0 ≤ discount i) : 0 ≤ pvBenefit benefit discount i := by sorry

end ActuarialValuation
