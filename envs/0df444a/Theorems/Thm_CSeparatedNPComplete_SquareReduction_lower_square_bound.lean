-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquareReduction_lower_square_bound
-- name    : CSeparatedNPComplete.SquareReduction.lower_square_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:50:15.119933+00:00
-- url     : https://prove2.me/theorems/d27837e3-cbd9-44a5-912d-0f3c4cdd4f65
-- title:
--   Square Reduction: lower square bound
-- statement:
--   The Square Reduction construction uses the lower square bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L139-L145
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L139-L145

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction

theorem CSeparatedNPComplete.SquareReduction.lower_square_bound {n : ℕ} (a : Fin n → ℕ) (i : Fin n) :
    (lower a i : ℝ) ^ 2 ≤ (a i : ℝ) ^ 2 * (base a : ℝ) ^ (2 * n) := by sorry
