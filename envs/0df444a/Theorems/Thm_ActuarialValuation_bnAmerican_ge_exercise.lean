-- Prove2me | Theorems.Thm_ActuarialValuation_bnAmerican_ge_exercise
-- name    : ActuarialValuation.bnAmerican_ge_exercise
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:38:10.694053+00:00
-- url     : https://prove2.me/theorems/562d9fc2-a288-448b-a57e-f554f91204e0
-- title:
--   Two-period binomial recursion and American option exercise: bnAmerican_ge_exercise
-- statement:
--   An American option holder can exercise immediately, so node value cannot be below intrinsic value.
--
--   Mathematical relation:
--
--   $$
--   bnAmerican\_ge\_exercise
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnAmericanNode

namespace ActuarialValuation

theorem bnAmerican_ge_exercise (exercise continuation : ℝ) : exercise ≤ bnAmericanNode exercise continuation := by sorry

end ActuarialValuation
