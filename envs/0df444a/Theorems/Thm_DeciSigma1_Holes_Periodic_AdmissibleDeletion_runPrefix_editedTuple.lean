-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_runPrefix_editedTuple
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.runPrefix_editedTuple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:42:47.020048+00:00
-- url     : https://prove2.me/theorems/fb688ab2-32c2-42f9-aca3-1a172a32ae30
-- title:
--   Admissible Deletion: run Prefix edited Tuple
-- statement:
--   At a cut that is not strictly inside an interval of deleted positions, the edited tuple has
--   the original state at the image of the cut.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L443-L448
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L443-L448

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
variable [Fintype S] (T : Table α S k) (hN : N = Fintype.card S)
include hN

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.runPrefix_editedTuple (l : Fin k) {c : ℕ} (hc : c ≤ (W l).length)
    (hint : c = 0 ∨ c ∉ deletedPositions W ρ N x l ∨ c - 1 ∉ deletedPositions W ρ N x l) :
    T.runPrefix (editedTuple W ρ N x) l (keepCut W ρ N x l c) = T.runPrefix W l c := by sorry
