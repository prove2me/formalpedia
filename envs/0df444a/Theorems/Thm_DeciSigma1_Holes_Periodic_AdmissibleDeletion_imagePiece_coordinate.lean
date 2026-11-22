-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_imagePiece_coordinate
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:41:53.008794+00:00
-- url     : https://prove2.me/theorems/ee9f4a99-94fa-4d33-a842-f650c28e65ff
-- title:
--   Admissible Deletion: image Piece coordinate
-- statement:
--   The Admissible Deletion construction uses the image Piece coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L366-L367
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L366-L367

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_coordinate (P : Piece W ρ.length) :
    (hx.imagePiece P).coordinate = P.coordinate := by sorry

attribute [defeq] DeciSigma1.Holes.Periodic.AdmissibleDeletion.imagePiece_coordinate
