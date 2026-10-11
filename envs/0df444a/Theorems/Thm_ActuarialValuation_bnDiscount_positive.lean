-- Prove2me | Theorems.Thm_ActuarialValuation_bnDiscount_positive
-- name    : ActuarialValuation.bnDiscount_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:34:44.783987+00:00
-- url     : https://prove2.me/theorems/76052a3f-7e43-41f1-ba77-fb269f6de14d
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnDiscount_positive
-- statement:
--   Positive riskless accumulation and a positive future cashflow imply a positive current bond value.
--
--   Mathematical relation:
--
--   $$
--   bnDiscount\_positive
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnDiscount

namespace ActuarialValuation

theorem bnDiscount_positive (R x : ℝ) (hR : 0 < R) (hx : 0 < x) : 0 < bnDiscount R x := by sorry

end ActuarialValuation
