-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquareReduction_root_product
-- name    : CSeparatedNPComplete.SquareReduction.root_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:50:00.752432+00:00
-- url     : https://prove2.me/theorems/9b7131ba-c260-4ed2-97ce-4329bff794de
-- title:
--   Square Reduction: root product
-- statement:
--   The Square Reduction construction uses the root product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L54-L59
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L54-L59

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Theorems.Thm_CSeparatedNPComplete_SquarePartition_root_product

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction

theorem CSeparatedNPComplete.SquareReduction.root_product {n : ℕ} (a : Fin n → ℕ) (i : Fin n) :
    upper a i * lower a i = a i * base a ^ (2 * n) := by sorry
