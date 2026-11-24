-- Prove2me | Theorems.Thm_FairSelling_PS_nonneg
-- name    : FairSelling.PS_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:23:18.679032+00:00
-- url     : https://prove2.me/theorems/caee47e5-eaf1-43cd-bb6e-1099df6b1fc1
-- title:
--   Fair Selling: PS nonneg
-- statement:
--   The Fair Selling construction uses the PS nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L58-L60
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L58-L60

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.PS_nonneg (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) : 0 ≤ PS n v p := by sorry
