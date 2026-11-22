-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_editedTuple_firstRejection
-- name    : DeciSigma1.Holes.Periodic.editedTuple_firstRejection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:47:44.006305+00:00
-- url     : https://prove2.me/theorems/4f549ac9-98f2-4faf-bb9a-c274d40cbf88
-- title:
--   Periodic: edited Tuple first Rejection
-- statement:
--   The first rejected cut of the edited tuple is the image of the first rejected cut of the
--   hole.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L872-L878
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L872-L878

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
variable [DecidableEq α] {S : Type} [Fintype S] [DecidableEq S] {W : Fin k → List α}
  {ρ : List α} {x : Piece W ρ.length → ℕ}

theorem DeciSigma1.Holes.Periodic.editedTuple_firstRejection (M : StructuralReader α S k) (hW : M.IsHole W)
    (hx : AdmissibleDeletion W ρ (Fintype.card S) x) (l : Fin k) :
    M.firstRejection (editedTuple W ρ (Fintype.card S) x) l =
      keepCut W ρ (Fintype.card S) x l (M.firstRejection W l) := by sorry
