-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_runPrefix_mod
-- name    : DeciSigma1.Holes.Periodic.Piece.runPrefix_mod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:45:00.243423+00:00
-- url     : https://prove2.me/theorems/e7e96340-d9de-461d-9fc9-c59cf2d45a8c
-- title:
--   Piece: run Prefix mod
-- statement:
--   The states of a piece at offsets of at least `stateTransientLength` that agree modulo
--   `statePeriodModulus` are equal.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L80-L95
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Pieces.lean#L80-L95

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
omit [DecidableEq α]

theorem DeciSigma1.Holes.Periodic.Piece.runPrefix_mod [Fintype S] (T : Table α S k) {d : ℕ} (P : Piece W d) {o₁ o₂ : ℕ}
    (h₁ : Periodic.stateTransientLength (Fintype.card S) d ≤ o₁)
        (h₂ : Periodic.stateTransientLength (Fintype.card S) d ≤ o₂)
    (h₁' : o₁ ≤ P.len) (h₂' : o₂ ≤ P.len)
        (hmod : o₁ % Periodic.statePeriodModulus (Fintype.card S) d =
      o₂ % Periodic.statePeriodModulus (Fintype.card S) d) :
    T.runPrefix W P.coordinate (P.start + o₁) = T.runPrefix W P.coordinate (P.start + o₂) := by sorry
