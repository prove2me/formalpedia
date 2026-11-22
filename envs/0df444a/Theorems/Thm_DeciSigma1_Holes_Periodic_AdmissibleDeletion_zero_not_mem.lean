-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_zero_not_mem
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.zero_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:45:44.459337+00:00
-- url     : https://prove2.me/theorems/d9a7dce9-4869-4df0-8c71-2e456ab85a7a
-- title:
--   Admissible Deletion: zero not mem
-- statement:
--   The Admissible Deletion construction uses the zero not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L607-L611
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L607-L611

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.zero_not_mem (l : Fin k) :
    0 ∉ deletedPositions W ρ N x l := by sorry
