-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquareReduction_values_eq_encode
-- name    : CSeparatedNPComplete.SquareReduction.values_eq_encode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:55:19.985851+00:00
-- url     : https://prove2.me/theorems/c43480d1-4786-42de-b023-1f87be269bef
-- title:
--   Square Reduction: values eq encode
-- statement:
--   The Square Reduction construction uses the values eq encode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L285-L290
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L285-L290

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction

theorem CSeparatedNPComplete.SquareReduction.values_eq_encode {n : ℕ} (a : Fin n → ℕ) :
    values a = fun i => (encode a i : ℝ) := by sorry
