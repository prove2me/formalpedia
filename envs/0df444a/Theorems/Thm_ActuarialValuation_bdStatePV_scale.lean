-- Prove2me | Theorems.Thm_ActuarialValuation_bdStatePV_scale
-- name    : ActuarialValuation.bdStatePV_scale
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:41:28.015017+00:00
-- url     : https://prove2.me/theorems/df22f907-6dc7-4d3c-9b77-03fd5aed68f4
-- title:
--   Finite-state stochastic discount factors and arbitrage-free valuation: bdStatePV_scale
-- statement:
--   State-contingent claim valuation is homogeneous in its cashflow amount.
--
--   Mathematical relation:
--
--   $$
--   bdStatePV\_scale
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

theorem bdStatePV_scale {m : ℕ} (p discount X : Fin m → ℝ) (a : ℝ) : bdStatePV p discount (fun ω => a*X ω) = a*bdStatePV p discount X := by sorry

end ActuarialValuation
