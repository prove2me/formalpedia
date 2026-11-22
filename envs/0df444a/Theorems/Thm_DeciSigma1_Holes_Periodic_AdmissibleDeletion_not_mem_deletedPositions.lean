-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_not_mem_deletedPositions
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.not_mem_deletedPositions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:04.553068+00:00
-- url     : https://prove2.me/theorems/891e72b9-2cd5-4273-8052-18ad87f7eff3
-- title:
--   Admissible Deletion: not mem deleted Positions
-- statement:
--   The Admissible Deletion construction uses the not mem deleted Positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L244-L252
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L244-L252

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.not_mem_deletedPositions (hx : AdmissibleDeletion W ρ N x) {l : Fin k}
    {p : ℕ}
    (Q : Piece W ρ.length) (hQl : Q.coordinate = l) (hQ1 : Q.start ≤ p) (hQ2 : p < Q.stop)
    (hns : p < Q.start + Periodic.boundaryMargin N ρ.length ∨ Q.start + Periodic.boundaryMargin N
        ρ.length + Periodic.statePeriodModulus N ρ.length * x Q ≤ p) :
    p ∉ deletedPositions W ρ N x l := by sorry
