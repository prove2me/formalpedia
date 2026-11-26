-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquareReduction_base_bound
-- name    : CSeparatedNPComplete.SquareReduction.base_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:55:41.214107+00:00
-- url     : https://prove2.me/theorems/3180b150-b335-55c1-840c-d1159f0cc8d2
-- title:
--   Square Reduction: base bound
-- statement:
--   The base itself has polynomial magnitude in the input count and maximum
--   weight. Its binary length is therefore linear in their binary lengths.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L316-L327
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L316-L327

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction

theorem CSeparatedNPComplete.SquareReduction.base_bound {n : ℕ} (a : Fin n → ℕ) (M : ℕ) (ha : ∀ i, a i ≤ M) :
    base a ≤ 2 + n + 2 * n * M + n * M ^ 2 := by sorry
