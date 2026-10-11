-- Prove2me | Theorems.Thm_ActuarialValuation_bdStatePV_empty
-- name    : ActuarialValuation.bdStatePV_empty
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:40:40.755439+00:00
-- url     : https://prove2.me/theorems/7d64f9f5-2142-408c-97dd-a13b0f1a9c6c
-- title:
--   Finite-state stochastic discount factors and arbitrage-free valuation: bdStatePV_empty
-- statement:
--   The empty sample space has zero raw state-price sum but cannot represent a normalised probability model.
--
--   Mathematical relation:
--
--   $$
--   bdStatePV\_empty
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdStatePV

namespace ActuarialValuation

theorem bdStatePV_empty (discount payoff : Fin 0 → ℝ) : bdStatePV (fun _ => 0) discount payoff = 0 := by sorry

end ActuarialValuation
