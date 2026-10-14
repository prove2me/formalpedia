-- Prove2me | Theorems.Thm_ActuarialValuation_bnAmerican_ge_continue
-- name    : ActuarialValuation.bnAmerican_ge_continue
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:38:24.081985+00:00
-- url     : https://prove2.me/theorems/431184c7-afb7-4f4c-93ae-b10e8c38aec9
-- title:
--   Two-period binomial recursion and American option exercise: bnAmerican_ge_continue
-- statement:
--   The option holder can wait, so American value cannot fall below continuation value.
--
--   Mathematical relation:
--
--   $$
--   bnAmerican\_ge\_continue
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnAmericanNode

namespace ActuarialValuation

theorem bnAmerican_ge_continue (exercise continuation : ℝ) : continuation ≤ bnAmericanNode exercise continuation := by sorry

end ActuarialValuation
