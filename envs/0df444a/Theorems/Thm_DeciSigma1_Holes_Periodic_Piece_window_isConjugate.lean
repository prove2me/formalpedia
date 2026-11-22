-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_window_isConjugate
-- name    : DeciSigma1.Holes.Periodic.Piece.window_isConjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:51:20.828937+00:00
-- url     : https://prove2.me/theorems/c31d6fd8-7bb4-4eb9-a0ca-ee8564913b81
-- title:
--   Piece: window is Conjugate
-- statement:
--   Every `d`-window of a piece is in the class of its root.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L121-L123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L121-L123

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
open DeciSigma1.Holes.Periodic.Piece
variable {W : Fin k → List α} {d : ℕ}

theorem DeciSigma1.Holes.Periodic.Piece.window_isConjugate (P : Piece W d) {z : ℕ} (hz : P.start ≤ z) (hze : z + d ≤ P.stop) :
    IsConjugate P.root (((W P.coordinate).drop z).take d) := by sorry
