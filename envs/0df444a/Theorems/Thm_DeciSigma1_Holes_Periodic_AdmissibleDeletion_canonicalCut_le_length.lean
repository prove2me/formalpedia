-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_canonicalCut_le_length
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_le_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:46:52.99147+00:00
-- url     : https://prove2.me/theorems/0881f7ac-995b-456e-b46c-1052fa6eb7ec
-- title:
--   Admissible Deletion: canonical Cut le length
-- statement:
--   The Admissible Deletion construction uses the canonical Cut le length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L367-L370
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L367-L370

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Periodic.AdmissibleDeletion
variable [DecidableEq α] {W : Fin k → List α} {ρ : List α} {N : ℕ} {x : Piece W ρ.length → ℕ}
variable (hx : AdmissibleDeletion W ρ N x)
include hx
omit hx

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.canonicalCut_le_length {l : Fin k} {c c' : ℕ} (h :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c c') :
    c' ≤ (editedTuple W ρ N x l).length := by sorry
