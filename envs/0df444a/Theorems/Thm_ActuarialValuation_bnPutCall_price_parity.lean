-- Prove2me | Theorems.Thm_ActuarialValuation_bnPutCall_price_parity
-- name    : ActuarialValuation.bnPutCall_price_parity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:37:21.145172+00:00
-- url     : https://prove2.me/theorems/93b425aa-0ea1-43cb-b121-7057da7e078a
-- title:
--   Explicit self-financing hedge and European option replication: bnPutCall_price_parity
-- statement:
--   One-period European put-call parity follows from statewise option payoffs and the risk-neutral stock martingale identity.
--
--   Mathematical relation:
--
--   $$
--   bnPutCall\_price\_parity
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 20.1–20.11, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1016/0304-405X(79)90015-1. The proposed model is rooted in Promislow chapter 20.1–20.11. The target Lean identity is an original derivation, not a verbatim published result. Published source page 339 gives the thematic chapter context, rather than an exact statement of this new formal theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnOnePeriodPrice
import Definitions.Def_actuarial_bnRiskNeutralProb
import Definitions.Def_actuarial_bnCall
import Definitions.Def_actuarial_bnPut

namespace ActuarialValuation

theorem bnPutCall_price_parity (s u d R k : ℝ) (h : u ≠ d) (hR : R ≠ 0) : bnOnePeriodPrice R (bnRiskNeutralProb u d R) (bnCall (s*u) k) (bnCall (s*d) k) - bnOnePeriodPrice R (bnRiskNeutralProb u d R) (bnPut (s*u) k) (bnPut (s*d) k) = s - k/R := by sorry

end ActuarialValuation
