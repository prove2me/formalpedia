-- Prove2me | Theorems.Thm_ActuarialValuation_bnPrice_add
-- name    : ActuarialValuation.bnPrice_add
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:34:18.957218+00:00
-- url     : https://prove2.me/theorems/6cc00458-a147-45db-96e8-51d48584b771
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnPrice_add
-- statement:
--   Arbitrage-free option prices are additive across equally dated claims.
--
--   Mathematical relation:
--
--   $$
--   bnPrice\_add
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnOnePeriodPrice

namespace ActuarialValuation

theorem bnPrice_add (R q xu xd yu yd : ℝ) : bnOnePeriodPrice R q (xu+yu) (xd+yd) = bnOnePeriodPrice R q xu xd + bnOnePeriodPrice R q yu yd := by sorry

end ActuarialValuation
