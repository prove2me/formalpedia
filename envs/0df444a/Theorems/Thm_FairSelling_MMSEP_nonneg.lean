-- Prove2me | Theorems.Thm_FairSelling_MMSEP_nonneg
-- name    : FairSelling.MMSEP_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:30:24.456512+00:00
-- url     : https://prove2.me/theorems/9679955f-aa5a-46d0-9ab9-7522458369dc
-- title:
--   Fair Selling: MMSEP nonneg
-- statement:
--   The Fair Selling construction uses the MMSEP nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L91-L93
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L91-L93

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.MMSEP_nonneg (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    0 ≤ MMSEP n v p := by sorry
