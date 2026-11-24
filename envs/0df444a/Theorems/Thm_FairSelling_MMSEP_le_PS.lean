-- Prove2me | Theorems.Thm_FairSelling_MMSEP_le_PS
-- name    : FairSelling.MMSEP_le_PS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:23:31.466405+00:00
-- url     : https://prove2.me/theorems/d97ac360-6770-4892-8101-8aa3d6e62d0a
-- title:
--   Fair Selling: MMSEP le PS
-- statement:
--   The Fair Selling construction uses the MMSEP le PS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L102-L104
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L102-L104

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.MMSEP_le_PS (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    MMSEP n v p ≤ PS n v p := by sorry
