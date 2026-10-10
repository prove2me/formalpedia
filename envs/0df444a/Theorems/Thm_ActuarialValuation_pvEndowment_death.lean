-- Prove2me | Theorems.Thm_ActuarialValuation_pvEndowment_death
-- name    : ActuarialValuation.pvEndowment_death
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:17:12.082988+00:00
-- url     : https://prove2.me/theorems/34d28229-3af2-42db-aa57-23f86d360aed
-- title:
--   Finite random present values of insurance benefits and premium streams: pvEndowment_death
-- statement:
--   An endowment contract pays the death contingent component when the covered death event occurs.
--
--   Mathematical relation:
--
--   $$
--   pvEndowment\_death
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvEndowmentBenefit

namespace ActuarialValuation

theorem pvEndowment_death (death maturityDiscount : ℝ) : pvEndowmentBenefit death maturityDiscount True = death := by sorry

end ActuarialValuation
