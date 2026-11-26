-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquareReduction_base_ge_two
-- name    : CSeparatedNPComplete.SquareReduction.base_ge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:47:27.930658+00:00
-- url     : https://prove2.me/theorems/16cad763-15d9-445d-9f26-62e51e0e4bfe
-- title:
--   Square Reduction: base ge two
-- statement:
--   The Square Reduction construction uses the base ge two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L35-L37
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L35-L37

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction

theorem CSeparatedNPComplete.SquareReduction.base_ge_two {n : ℕ} (a : Fin n → ℕ) : 2 ≤ base a := by sorry
