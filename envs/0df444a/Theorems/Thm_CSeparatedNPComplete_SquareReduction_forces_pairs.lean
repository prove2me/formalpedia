-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquareReduction_forces_pairs
-- name    : CSeparatedNPComplete.SquareReduction.forces_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:49:58.45875+00:00
-- url     : https://prove2.me/theorems/83c5d881-d458-5e61-8e62-d940ce76a44b
-- title:
--   Square Reduction: forces pairs
-- statement:
--   Equal sums force one member of every pair onto each side. The hypothesis
--   does not assume equal cardinalities or a paired form of the selector.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L149-L199
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L149-L199

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction

theorem CSeparatedNPComplete.SquareReduction.forces_pairs {n : ℕ} (a : Fin n → ℕ) (p q : Vec n)
    (hp : is_binary p) (hq : is_binary q)
    (hbal : dot (Fin.append p q) (values a) = dot (values a) 1 / 2) :
    ∀ i, p i + q i = 1 := by sorry
