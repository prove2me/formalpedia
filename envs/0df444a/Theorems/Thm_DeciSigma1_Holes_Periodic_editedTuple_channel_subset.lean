-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_editedTuple_channel_subset
-- name    : DeciSigma1.Holes.Periodic.editedTuple_channel_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:47:38.937917+00:00
-- url     : https://prove2.me/theorems/328a5193-0061-49c6-b046-c7a5b9c4cec6
-- title:
--   Periodic: edited Tuple channel subset
-- statement:
--   Every channel of the edited tuple, including those from a coordinate to itself and those
--   with empty target suffixes, is contained in the channel of the original tuple.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L843-L851
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Transport.lean#L843-L851

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

theorem DeciSigma1.Holes.Periodic.editedTuple_channel_subset (T : Table α S k)
    (hx : AdmissibleDeletion W ρ (Fintype.card S) x) (i j : Fin k) :
    T.channel (editedTuple W ρ (Fintype.card S) x) i j ⊆ T.channel W i j := by sorry
