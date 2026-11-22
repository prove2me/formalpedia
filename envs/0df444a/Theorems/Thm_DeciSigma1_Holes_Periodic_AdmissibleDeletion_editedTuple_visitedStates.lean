-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_editedTuple_visitedStates
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.editedTuple_visitedStates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:45:58.214486+00:00
-- url     : https://prove2.me/theorems/4aba63ae-4bc0-4328-9996-991140d98848
-- title:
--   Admissible Deletion: edited Tuple visited States
-- statement:
--   The edited tuple visits only states that the original visits.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L820-L826
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L820-L826

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.editedTuple_visitedStates [Fintype S] [DecidableEq S] (T : Table α S k)
    (hN : N = Fintype.card S)
    (l : Fin k) : T.visitedStates (editedTuple W ρ N x) l ⊆ T.visitedStates W l := by sorry
