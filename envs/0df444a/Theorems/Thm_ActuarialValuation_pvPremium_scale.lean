-- Prove2me | Theorems.Thm_ActuarialValuation_pvPremium_scale
-- name    : ActuarialValuation.pvPremium_scale
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:16:05.02399+00:00
-- url     : https://prove2.me/theorems/b22944ba-2d09-4601-8a09-692f50150cf0
-- title:
--   Finite random present values of insurance benefits and premium streams: pvPremium_scale
-- statement:
--   Premium present values scale linearly in the annual premium rate.
--
--   Mathematical relation:
--
--   $$
--   pvPremium\_scale
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvPremium

namespace ActuarialValuation

theorem pvPremium_scale {n : ℕ} (annuity : Fin n → ℝ) (p a : ℝ) (i : Fin n) : pvPremium annuity (a*p) i = a * pvPremium annuity p i := by sorry

end ActuarialValuation
