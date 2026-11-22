-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_eq_of_followerEdge
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.eq_of_followerEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:46:11.914401+00:00
-- url     : https://prove2.me/theorems/28b23af3-6036-4b2a-aed4-1b4a6594fdcb
-- title:
--   Admissible Deletion: eq of follower Edge
-- statement:
--   The Admissible Deletion construction uses the eq of follower Edge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L870-L878
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L870-L878

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.eq_of_followerEdge {P Q : Piece W ρ.length} (hP : P ∈ piecesOf W ρ) (hQ : Q ∈ piecesOf W ρ)
    (hG : FollowerEdge P Q)
        (heq : retainedLength (N := N) (x := x) P = retainedLength (N := N) (x := x) Q) :
    x P = x Q ∧ P.len = Q.len := by sorry
