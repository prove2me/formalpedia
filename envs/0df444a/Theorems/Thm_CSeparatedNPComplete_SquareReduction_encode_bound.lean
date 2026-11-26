-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquareReduction_encode_bound
-- name    : CSeparatedNPComplete.SquareReduction.encode_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:55:38.104796+00:00
-- url     : https://prove2.me/theorems/a1209c60-5df5-5105-89e7-19c6463c3128
-- title:
--   Square Reduction: encode bound
-- statement:
--   A numerical bound giving polynomial binary output length: there are `2*n`
--   entries, each with at most `4*(n+1)*log₂ K + 1` bits.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L294-L312
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L294-L312

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction

theorem CSeparatedNPComplete.SquareReduction.encode_bound {n : ℕ} (a : Fin n → ℕ) (i : Fin (n + n)) :
    encode a i ≤ base a ^ (4 * (n + 1)) := by sorry
