-- Prove2me | Theorems.Thm_ActuarialValuation_pvPremium_zero
-- name    : ActuarialValuation.pvPremium_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:15:51.344078+00:00
-- url     : https://prove2.me/theorems/648a3241-f09f-4b9e-9917-97329510cffa
-- title:
--   Finite random present values of insurance benefits and premium streams: pvPremium_zero
-- statement:
--   Zero premium rate yields no premium present value in every scenario.
--
--   Mathematical relation:
--
--   $$
--   pvPremium\_zero
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvPremium

namespace ActuarialValuation

theorem pvPremium_zero {n : ℕ} (annuity : Fin n → ℝ) (i : Fin n) : pvPremium annuity 0 i = 0 := by sorry

end ActuarialValuation
