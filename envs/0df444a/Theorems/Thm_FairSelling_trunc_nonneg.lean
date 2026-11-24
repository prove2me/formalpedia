-- Prove2me | Theorems.Thm_FairSelling_trunc_nonneg
-- name    : FairSelling.trunc_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:42.507843+00:00
-- url     : https://prove2.me/theorems/5925c737-1086-4987-a586-685774df18c5
-- title:
--   Fair Selling: trunc nonneg
-- statement:
--   The Fair Selling construction uses the trunc nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L58-L59
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L58-L59

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

theorem FairSelling.trunc_nonneg (w p : G → ℝ) (t : ℝ) (hp : ∀ g, 0 ≤ p g) (g : G) : 0 ≤ trunc w p t g := by sorry
