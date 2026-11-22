-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_canonicalCut_end_sub
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_end_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:45:36.892821+00:00
-- url     : https://prove2.me/theorems/9e387155-8e78-4790-a600-76dd256bd60f
-- title:
--   Admissible Deletion: canonical Cut end sub
-- statement:
--   The cut `|ρ|` letters before the end of a piece is the canonical original cut of the cut
--   `|ρ|` letters before the end of its image.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L564-L583
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L564-L583

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_end_sub (P : Piece W ρ.length) :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) P.coordinate (P.stop - ρ.length)
        ((hx.imagePiece P).stop - ρ.length) := by sorry
