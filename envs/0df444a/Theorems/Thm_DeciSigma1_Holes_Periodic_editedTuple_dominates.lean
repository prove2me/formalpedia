-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_editedTuple_dominates
-- name    : DeciSigma1.Holes.Periodic.editedTuple_dominates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:47:44.812999+00:00
-- url     : https://prove2.me/theorems/2e9eeba2-b04c-4a7f-9b5d-adddcffca81c
-- title:
--   Periodic: edited Tuple dominates
-- statement:
--   The edited tuple dominates the original one: equal endpoints, fewer visited states and
--   smaller channels.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L855-L859
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L855-L859

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

theorem DeciSigma1.Holes.Periodic.editedTuple_dominates (T : Table α S k)
    (hx : AdmissibleDeletion W ρ (Fintype.card S) x) :
    Dominates T (editedTuple W ρ (Fintype.card S) x) W := by sorry
