-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_length_editedTuple
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.length_editedTuple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:42:02.187557+00:00
-- url     : https://prove2.me/theorems/f336d804-54b4-4104-885e-e60af44f74c1
-- title:
--   Admissible Deletion: length edited Tuple
-- statement:
--   The Admissible Deletion construction uses the length edited Tuple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L512-L514
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L512-L514

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
omit hx

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.length_editedTuple (l : Fin k) :
    (editedTuple W ρ N x l).length = keepCut W ρ N x l (W l).length := by sorry
