-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquareReduction_lower_lt_upper
-- name    : CSeparatedNPComplete.SquareReduction.lower_lt_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:47:23.528803+00:00
-- url     : https://prove2.me/theorems/b9ca49ac-6536-548f-b708-e36c4d140ad2
-- title:
--   Square Reduction: lower lt upper
-- statement:
--   The Square Reduction construction uses the lower lt upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L44-L52
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L44-L52

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction

theorem CSeparatedNPComplete.SquareReduction.lower_lt_upper {n : ℕ} (a : Fin n → ℕ) (i : Fin n) : lower a i < upper a i := by sorry
