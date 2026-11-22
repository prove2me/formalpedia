-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_Piece_dvd_of_periodicOn
-- name    : DeciSigma1.Holes.Periodic.Piece.dvd_of_periodicOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:00.287799+00:00
-- url     : https://prove2.me/theorems/27f7028f-6791-4f63-9eca-2e1a048bedc3
-- title:
--   Piece: dvd of periodic On
-- statement:
--   In a piece of primitive period `d`, a second period `δ` on a stretch of length `≥ d + δ`
--   from inside the piece to its end is a multiple of `d`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L127-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L127-L148

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

theorem DeciSigma1.Holes.Periodic.Piece.dvd_of_periodicOn
    (P : Piece W d) {x δ : ℕ}
    (hx : P.start ≤ x) (hδ : PeriodicOn (W P.coordinate) δ x P.stop)
        (hlen : x + d + δ ≤ P.stop) : d ∣ δ := by sorry
