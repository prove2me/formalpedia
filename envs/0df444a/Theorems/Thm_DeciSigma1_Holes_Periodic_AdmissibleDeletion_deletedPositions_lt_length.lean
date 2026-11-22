-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_deletedPositions_lt_length
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.deletedPositions_lt_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:28.071337+00:00
-- url     : https://prove2.me/theorems/c0d30128-664a-482c-9294-91cf595fdf46
-- title:
--   Admissible Deletion: deleted Positions lt length
-- statement:
--   The Admissible Deletion construction uses the deleted Positions lt length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L254-L262
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L254-L262

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
variable [DecidableEq α]
variable (W : Fin k → List α) (ρ : List α) (N : ℕ) (x : Piece W ρ.length → ℕ)
variable {W ρ N x}

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.deletedPositions_lt_length (hx : AdmissibleDeletion W ρ N x) {l : Fin k}
    {p : ℕ}
    (hp : p ∈ deletedPositions W ρ N x l) : p < (W l).length := by sorry
