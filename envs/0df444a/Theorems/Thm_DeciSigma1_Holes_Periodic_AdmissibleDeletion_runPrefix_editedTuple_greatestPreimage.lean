-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_AdmissibleDeletion_runPrefix_editedTuple_greatestPreimage
-- name    : DeciSigma1.Holes.Periodic.AdmissibleDeletion.runPrefix_editedTuple_greatestPreimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:45:13.175025+00:00
-- url     : https://prove2.me/theorems/0c47f630-f513-40c2-a692-04bbc3f92fe1
-- title:
--   Admissible Deletion: run Prefix edited Tuple greatest Preimage
-- statement:
--   The state of the edited tuple at a cut is the original state at the greatest preimage of
--   the cut.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L452-L456
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L452-L456

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

theorem DeciSigma1.Holes.Periodic.AdmissibleDeletion.runPrefix_editedTuple_greatestPreimage (l : Fin k) (a : ℕ) :
    T.runPrefix (editedTuple W ρ N x) l a =
      T.runPrefix W l (greatestPreimage (deletedPositions W ρ N x l) a) := by sorry
