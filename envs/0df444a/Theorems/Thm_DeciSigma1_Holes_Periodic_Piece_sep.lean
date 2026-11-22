-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_sep
-- name    : DeciSigma1.Holes.Periodic.Piece.sep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:58.270583+00:00
-- url     : https://prove2.me/theorems/8a1cb4ac-a5b2-4eb6-84ea-29fe5251a7f6
-- title:
--   Piece: sep
-- statement:
--   Distinct pieces of one word: the earlier one ends less than `d` letters after the later
--   one starts, so starts and ends are ordered alike.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L288-L296
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L288-L296

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}
variable {W : Fin k → List α} {d : ℕ}

theorem DeciSigma1.Holes.Periodic.Piece.sep {P Q : Piece W d} (hne : P ≠ Q) (hl : P.coordinate = Q.coordinate)
    (hs : P.start ≤ Q.start) :
    P.start < Q.start ∧ P.stop < Q.start + d ∧ P.stop + d < Q.stop := by sorry
