-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_piece_ends_sep
-- name    : DeciSigma1.Holes.Periodic.piece_ends_sep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:06:58.889989+00:00
-- url     : https://prove2.me/theorems/32a38ec4-18fd-4d11-879d-75aeba6f5da1
-- title:
--   Periodic: piece ends sep
-- statement:
--   The ends of distinct pieces of period `d` in one word are more than `d` apart.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L299-L303
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L299-L303

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

theorem DeciSigma1.Holes.Periodic.piece_ends_sep {P Q : Piece W d} (hne : P ≠ Q) (hl : P.coordinate = Q.coordinate) :
    d < (P.stop : ℤ) - Q.stop ∨ d < (Q.stop : ℤ) - P.stop := by sorry
