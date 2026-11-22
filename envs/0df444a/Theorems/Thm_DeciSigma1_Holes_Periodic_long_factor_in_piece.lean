-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Periodic_long_factor_in_piece
-- name    : DeciSigma1.Holes.Periodic.long_factor_in_piece
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:47.7248+00:00
-- url     : https://prove2.me/theorems/58a1898f-7832-4688-bac0-c07566952c79
-- title:
--   Periodic: long factor in piece
-- statement:
--   An interval of length at least `2p` with period `p` lies in a piece whose period is the
--   least period `d` of the interval, and `d ∣ p`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L389-L408
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Periodic/Basic.lean#L389-L408

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

theorem DeciSigma1.Holes.Periodic.long_factor_in_piece [DecidableEq α] (W : Fin k → List α) (l : Fin k) {p x y : ℕ}
    (hp : 0 < p) (hy : y ≤ (W l).length) (hlen : x + 2 * p ≤ y) (hper : PeriodicOn (W l) p x y) :
    ∃ P : Piece W (leastPeriod (((W l).drop x).take (y - x))), P.coordinate = l ∧ P.start ≤ x ∧ y ≤
        P.stop ∧
      leastPeriod (((W l).drop x).take (y - x)) ∣ p := by sorry
