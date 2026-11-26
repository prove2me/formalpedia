-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquareReduction_values_perfect_square
-- name    : CSeparatedNPComplete.SquareReduction.values_perfect_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:50:16.645412+00:00
-- url     : https://prove2.me/theorems/5cd46777-2611-5f53-9734-f4d4d884932f
-- title:
--   Square Reduction: values perfect square
-- statement:
--   The Square Reduction construction uses the values perfect square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L258-L266
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L258-L266

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Theorems.Thm_CSeparatedNPComplete_SquarePartition_values_perfect_square

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction

theorem CSeparatedNPComplete.SquareReduction.values_perfect_square {n : ℕ} (a : Fin n → ℕ) : perf_square_vec (values a) := by sorry
