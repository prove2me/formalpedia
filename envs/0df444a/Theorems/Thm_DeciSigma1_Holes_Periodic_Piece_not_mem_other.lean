-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_not_mem_other
-- name    : DeciSigma1.Holes.Periodic.Piece.not_mem_other
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:05.987806+00:00
-- url     : https://prove2.me/theorems/4b9d7480-6aae-40ae-bf8c-7ddc04ae49cb
-- title:
--   Piece: not mem other
-- statement:
--   A position of a piece outside its first and last `d` letters lies in no other piece of
--   the same word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L307-L313
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L307-L313

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

theorem DeciSigma1.Holes.Periodic.Piece.not_mem_other {P Q : Piece W d} (hne : P ≠ Q) (hl : P.coordinate = Q.coordinate)
    {p : ℕ}
    (hp1 : P.start + d ≤ p) (hp2 : p + d < P.stop) : ¬ (Q.start ≤ p ∧ p < Q.stop) := by sorry
