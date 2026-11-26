-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquareReduction_paired_card
-- name    : CSeparatedNPComplete.SquareReduction.paired_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:50:13.325121+00:00
-- url     : https://prove2.me/theorems/a1735f89-943f-43ff-997d-cc1d5f19df95
-- title:
--   Square Reduction: paired card
-- statement:
--   The Square Reduction construction uses the paired card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L213-L218
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L213-L218

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction

theorem CSeparatedNPComplete.SquareReduction.paired_card {n : ℕ} (p : Vec n) :
    dot (Fin.append p (1 - p)) 1 = ((n + n : ℕ) : ℝ) / 2 := by sorry
