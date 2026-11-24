-- Prove2me | Theorems.Thm_FairSelling_truncBundle_nonneg
-- name    : FairSelling.truncBundle_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:32:16.773196+00:00
-- url     : https://prove2.me/theorems/0519de13-84d3-40f3-be6a-893f0565045f
-- title:
--   Fair Selling: trunc Bundle nonneg
-- statement:
--   The Fair Selling construction uses the trunc Bundle nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L67-L69
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L67-L69

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]

theorem FairSelling.truncBundle_nonneg (w p : G → ℝ) (t : ℝ) (hp : ∀ g, 0 ≤ p g) (R : Finset G) :
    0 ≤ truncBundle w p t R := by sorry
