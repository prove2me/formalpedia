-- Prove2me | Theorems.Thm_DeciSigma1_Words_PeriodicOn_window_rotate
-- name    : DeciSigma1.Words.PeriodicOn.window_rotate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:09.997728+00:00
-- url     : https://prove2.me/theorems/97736251-d403-48c9-971a-1c9c45c18f1d
-- title:
--   Periodic On: window rotate
-- statement:
--   In an interval with period `d`, the factor of length `d` at `z` is a rotation of the factor
--   of length `d` at the start of the interval.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L192-L212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L192-L212

module
public import Mathlib.Data.List.PeriodicityLemma
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
variable {α : Type*}
open DeciSigma1.Words.PeriodicOn
variable {w : List α} {d s e : ℕ}

theorem DeciSigma1.Words.PeriodicOn.window_rotate (h : PeriodicOn w d s e) (he : e ≤ w.length) {z : ℕ} (hsz : s ≤ z)
    (hz : z + d ≤ e) : (w.drop z).take d = ((w.drop s).take d).rotate ((z - s) % d) := by sorry
