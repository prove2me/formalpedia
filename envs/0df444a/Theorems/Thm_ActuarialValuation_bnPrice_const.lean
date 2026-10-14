-- Prove2me | Theorems.Thm_ActuarialValuation_bnPrice_const
-- name    : ActuarialValuation.bnPrice_const
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:34:04.459057+00:00
-- url     : https://prove2.me/theorems/6b266295-7845-4414-9139-31668a3bbed5
-- title:
--   One-period market no-arbitrage and risk-neutral probability: bnPrice_const
-- statement:
--   A deterministic terminal cashflow is valued by discounting it at the bank return.
--
--   Mathematical relation:
--
--   $$
--   bnPrice\_const
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnOnePeriodPrice

namespace ActuarialValuation

theorem bnPrice_const (R q x : ℝ) : bnOnePeriodPrice R q x x = x/R := by sorry

end ActuarialValuation
