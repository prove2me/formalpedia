-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquareReduction_values_positive
-- name    : CSeparatedNPComplete.SquareReduction.values_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:50:28.237395+00:00
-- url     : https://prove2.me/theorems/2198a0e5-8d90-404e-99b2-205fd09b542a
-- title:
--   Square Reduction: values positive
-- statement:
--   The Square Reduction construction uses the values positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L268-L278
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L268-L278

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction

theorem CSeparatedNPComplete.SquareReduction.values_positive {n : ℕ} (a : Fin n → ℕ) : ∀ i, 0 < values a i := by sorry
