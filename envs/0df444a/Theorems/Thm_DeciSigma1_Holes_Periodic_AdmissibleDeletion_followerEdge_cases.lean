-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_followerEdge_cases
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.followerEdge_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:42:53.898804+00:00
-- url     : https://prove2.me/theorems/f806579f-25e5-47fe-ae9c-4b6ff8e71037
-- title:
--   Admissible Deletion: follower Edge cases
-- statement:
--   Two pieces joined by a follower edge lose the same number of blocks, or one is shorter than
--   the other by at least `comparisonGap` both before and after the deletion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L845-L857
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L845-L857

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.followerEdge_cases {P Q : Piece W ρ.length} (hP : P ∈ piecesOf W ρ) (hQ : Q ∈ piecesOf W ρ)
    (hG : FollowerEdge P Q) : x P = x Q ∨
      (P.len + Periodic.comparisonGap N ρ.length ≤ Q.len ∧
        retainedLength (N := N) (x := x) P + Periodic.comparisonGap N ρ.length ≤ retainedLength
            (N := N) (x := x) Q) ∨
      (Q.len + Periodic.comparisonGap N ρ.length ≤ P.len ∧
        retainedLength (N := N) (x := x) Q + Periodic.comparisonGap N ρ.length ≤ retainedLength
            (N := N) (x := x) P) := by sorry
