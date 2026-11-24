-- Prove2me | Theorems.Thm_FairSelling_MMSEPset_bddAbove
-- name    : FairSelling.MMSEPset_bddAbove
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:23:10.178933+00:00
-- url     : https://prove2.me/theorems/f7188195-520b-420f-841c-a1bbdbbe81d1
-- title:
--   Fair Selling: MMSEPset bdd Above
-- statement:
--   The Fair Selling construction uses the MMSEPset bdd Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L74-L76
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L74-L76

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.MMSEPset_bddAbove (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    BddAbove (MMSEPset n v p) := by sorry
