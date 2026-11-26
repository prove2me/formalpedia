-- Prove2me | Theorems.Thm_CSeparatedNPComplete_SquareReduction_paired_balance_identity
-- name    : CSeparatedNPComplete.SquareReduction.paired_balance_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:50:09.282751+00:00
-- url     : https://prove2.me/theorems/bfb67183-48c6-447b-af00-355b07cd5396
-- title:
--   Square Reduction: paired balance identity
-- statement:
--   The Square Reduction construction uses the paired balance identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L201-L211
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/SquareReduction.lean#L201-L211

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction

theorem CSeparatedNPComplete.SquareReduction.paired_balance_identity {n : ℕ} (a : Fin n → ℕ) (p : Vec n) :
    dot (Fin.append p (1 - p)) (values a) - dot (values a) 1 / 2 =
      4 * (base a : ℝ) ^ (2 * n) *
        (dot p (fun i => (a i : ℝ)) - (∑ i, (a i : ℝ)) / 2) := by sorry
