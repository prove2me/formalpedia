-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_len_eq_retainedLength_add
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.len_eq_retainedLength_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:42:51.630851+00:00
-- url     : https://prove2.me/theorems/09131846-35da-43b2-b516-3ddc35b2172c
-- title:
--   Admissible Deletion: len eq retained Length add
-- statement:
--   The Admissible Deletion construction uses the len eq retained Length add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L830-L835
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L830-L835

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.len_eq_retainedLength_add (P : Piece W ρ.length) :
    P.len = retainedLength (N := N) (x := x) P + Periodic.statePeriodModulus N ρ.length * x P := by sorry
