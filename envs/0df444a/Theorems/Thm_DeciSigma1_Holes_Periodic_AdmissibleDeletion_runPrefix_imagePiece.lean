-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_runPrefix_imagePiece
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.runPrefix_imagePiece
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:43:27.411798+00:00
-- url     : https://prove2.me/theorems/8c18efef-0f6c-41eb-9ff3-7e849c220961
-- title:
--   Admissible Deletion: run Prefix image Piece
-- statement:
--   The states of the image of a piece are its original states at the same offsets.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L459-L490
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L459-L490

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
variable [Fintype S] (T : Table α S k) (hN : N = Fintype.card S)
include hN

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.runPrefix_imagePiece (P : Piece W ρ.length) {o : ℕ}
    (ho : o ≤ retainedLength (N := N) (x := x) P) :
    T.runPrefix (editedTuple W ρ N x) P.coordinate ((hx.imagePiece P).start + o) =
        T.runPrefix W P.coordinate (P.start + o) := by sorry
