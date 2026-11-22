-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_retainedCount_junction
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.retainedCount_junction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:43:36.115943+00:00
-- url     : https://prove2.me/theorems/10f18060-cea6-45c2-a9c4-75cc27e74c56
-- title:
--   Admissible Deletion: retained Count junction
-- statement:
--   The junction of a shortened piece: the image of the start of its site.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L599-L604
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L599-L604

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α S : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable {N : ℕ} {x : Piece W ρ.length → ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.retainedCount_junction (P : Piece W ρ.length) (hxP : x P ≠ 0) :
    keepCut W ρ N x P.coordinate (P.start + Periodic.boundaryMargin N ρ.length) =
        (hx.imagePiece P).start + Periodic.boundaryMargin N ρ.length := by sorry
