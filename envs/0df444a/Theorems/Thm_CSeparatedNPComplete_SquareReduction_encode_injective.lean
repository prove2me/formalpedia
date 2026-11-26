-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquareReduction_encode_injective
-- name    : CSeparatedNPComplete.SquareReduction.encode_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:55:46.905181+00:00
-- url     : https://prove2.me/theorems/fdd34e25-e762-4159-9a42-bccfa298e6fc
-- title:
--   Square Reduction: encode injective
-- statement:
--   The ordered encoding is one-to-one, in addition to preserving yes/no
--   answers. Karp (many-one) reducibility itself does not require injectivity.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L331-L355
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L331-L355

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction

theorem CSeparatedNPComplete.SquareReduction.encode_injective (n : ℕ) : Function.Injective (@encode n) := by sorry
