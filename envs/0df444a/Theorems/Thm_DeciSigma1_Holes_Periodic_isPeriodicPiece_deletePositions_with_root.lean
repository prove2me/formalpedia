-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_isPeriodicPiece_deletePositions_with_root
-- name    : DeciSigma1.Holes.Periodic.isPeriodicPiece_deletePositions_with_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:59.825123+00:00
-- url     : https://prove2.me/theorems/44fe7eb1-86d6-4d1a-a637-c1508091b111
-- title:
--   Periodic: is Periodic Piece delete Positions with root
-- statement:
--   If no position of a piece is deleted, and neither are the letters just before and after it,
--   the retained interval is a piece of the edited word with the same period, at the images of the
--   original cuts. Its root text and interval length are unchanged.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L90-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L90-L155

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Periodic.isPeriodicPiece_deletePositions_with_root {U U' : Fin k → List α} {l : Fin k}
    {Dl : Finset ℕ}
    (hU' : U' l = deletePositions (U l) Dl) {d s e : ℕ} (hc : IsPeriodicPiece U d l s e)
    (hin : ∀ p, s ≤ p → p < e → p ∉ Dl) (hleft : s ≠ 0 → s - 1 ∉ Dl)
    (hright : e < (U l).length → e ∉ Dl) :
    IsPeriodicPiece U' d l (retainedCount Dl s) (retainedCount Dl e) ∧ retainedCount Dl e =
        retainedCount Dl s + (e - s) ∧
      ((U' l).drop (retainedCount Dl s)).take d = ((U l).drop s).take d := by sorry
