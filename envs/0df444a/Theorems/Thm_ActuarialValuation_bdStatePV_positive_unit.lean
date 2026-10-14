-- Prove2me | Theorems.Thm_ActuarialValuation_bdStatePV_positive_unit
-- name    : ActuarialValuation.bdStatePV_positive_unit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:41:53.269885+00:00
-- url     : https://prove2.me/theorems/872357f2-f00f-465e-8277-4ab87696bcf0
-- title:
--   Finite-state stochastic discount factors and arbitrage-free valuation: bdStatePV_positive_unit
-- statement:
--   A positive pricing kernel with positive mass in at least one scenario gives a strictly positive certain unit bond price.
--
--   Mathematical relation:
--
--   $$
--   bdStatePV\_positive\_unit
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 2.12–2.13 and 20.13, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.jstor.org/stable/2951677. The proposed model is rooted in Promislow chapter 2.12–2.13 and 20.13. The target Lean identity is an original derivation, not a verbatim published result. Published source page 367 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdStateZeroBond

namespace ActuarialValuation

theorem bdStatePV_positive_unit {m : ℕ} (p discount : Fin m → ℝ) (hp : ∀ ω,0≤p ω) (hd : ∀ ω,0<discount ω) (hpos : ∃ ω, 0<p ω) : 0<bdStateZeroBond p discount := by sorry

end ActuarialValuation
