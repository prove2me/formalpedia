-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquareReduction_weight_lt_base
-- name    : CSeparatedNPComplete.SquareReduction.weight_lt_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:49:47.070218+00:00
-- url     : https://prove2.me/theorems/c132f4b6-8388-5a75-9950-013b5a5892b8
-- title:
--   Square Reduction: weight lt base
-- statement:
--   The Square Reduction construction uses the weight lt base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L39-L42
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L39-L42

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction

theorem CSeparatedNPComplete.SquareReduction.weight_lt_base {n : ℕ} (a : Fin n → ℕ) (i : Fin n) : a i < base a := by sorry
