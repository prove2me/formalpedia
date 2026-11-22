-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_comparisonGap_pos
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.comparisonGap_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:44:06.468797+00:00
-- url     : https://prove2.me/theorems/8a7fea8d-a89f-44b1-a636-6c03267a2fed
-- title:
--   Admissible Deletion: comparison Gap pos
-- statement:
--   The Admissible Deletion construction uses the comparison Gap pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L838-L841
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L838-L841

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
omit [DecidableEq α] hx

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.comparisonGap_pos (P : Piece W ρ.length) :
    0 < Periodic.comparisonGap N ρ.length := by sorry
