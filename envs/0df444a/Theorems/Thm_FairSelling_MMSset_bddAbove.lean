-- Prove2me | Theorems.Thm_FairSelling_MMSset_bddAbove
-- name    : FairSelling.MMSset_bddAbove
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:37:12.979633+00:00
-- url     : https://prove2.me/theorems/3dcce65c-6a27-44de-ae94-95f49b1cfe87
-- title:
--   Fair Selling: MMSset bdd Above
-- statement:
--   The Fair Selling construction uses the MMSset bdd Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L70-L72
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L70-L72

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.MMSset_bddAbove (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    BddAbove (MMSset n v p) := by sorry
