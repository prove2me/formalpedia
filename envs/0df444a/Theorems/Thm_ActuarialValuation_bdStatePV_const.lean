-- Prove2me | Theorems.Thm_ActuarialValuation_bdStatePV_const
-- name    : ActuarialValuation.bdStatePV_const
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:40:58.927451+00:00
-- url     : https://prove2.me/theorems/6bc68870-82d5-49e7-8136-94bb51ca9267
-- title:
--   Finite-state stochastic discount factors and arbitrage-free valuation: bdStatePV_const
-- statement:
--   A deterministic one-period payoff is priced using the state-price value of a one-unit certain redemption.
--
--   Mathematical relation:
--
--   $$
--   bdStatePV\_const
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdStatePV
import Definitions.Def_actuarial_bdStateZeroBond

namespace ActuarialValuation

theorem bdStatePV_const {m : ℕ} (p discount : Fin m → ℝ) (a : ℝ) : bdStatePV p discount (fun _ => a) = a * bdStateZeroBond p discount := by sorry

end ActuarialValuation
