-- Prove2me | Theorems.Thm_DeciSigma1_Words_period_extend_gcd
-- name    : DeciSigma1.Words.period_extend_gcd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:22.58287+00:00
-- url     : https://prove2.me/theorems/1fbd98b3-345e-4ae3-810a-5301e1fb4f2c
-- title:
--   Words: period extend gcd
-- statement:
--   Fine–Wilf on a common interval: an interval of length at least `p + q - gcd p q` with
--   periods `p` and `q` has period `gcd p q`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L243-L248
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L243-L248

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

theorem DeciSigma1.Words.period_extend_gcd {w : List α} {p q s e : ℕ} (hse : s ≤ e) (he : e ≤ w.length)
    (hp : PeriodicOn w p s e) (hq : PeriodicOn w q s e) (hlen : p + q - p.gcd q ≤ e - s) :
    PeriodicOn w (p.gcd q) s e := by sorry
