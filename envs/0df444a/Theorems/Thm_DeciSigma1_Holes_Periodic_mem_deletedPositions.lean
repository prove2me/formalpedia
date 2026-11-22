-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_mem_deletedPositions
-- name    : DeciSigma1.Holes.Periodic.mem_deletedPositions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:39.737814+00:00
-- url     : https://prove2.me/theorems/439a7e67-1221-452b-868c-f1e073d9060f
-- title:
--   Periodic: mem deleted Positions
-- statement:
--   The Periodic construction uses the mem deleted Positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L202-L210
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Deletion.lean#L202-L210

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

theorem DeciSigma1.Holes.Periodic.mem_deletedPositions {l : Fin k} {p : ℕ} : p ∈ deletedPositions W ρ N x l ↔
    ∃ P ∈ piecesOf W ρ, P.coordinate = l ∧ P.start + Periodic.boundaryMargin N ρ.length ≤ p ∧
      p < P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length *
          x P := by sorry
