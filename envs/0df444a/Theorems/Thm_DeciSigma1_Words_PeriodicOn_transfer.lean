-- Prove2me | Theorems.Thm_DeciSigma1_Words_PeriodicOn_transfer
-- name    : DeciSigma1.Words.PeriodicOn.transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:48.11681+00:00
-- url     : https://prove2.me/theorems/8482af07-6a8d-4c86-9998-43c8225852c9
-- title:
--   Periodic On: transfer
-- statement:
--   A period on an interval transfers to every word with the same letters below its end.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L234-L239
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L234-L239

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

theorem DeciSigma1.Words.PeriodicOn.transfer {w w' : List α} {p s e : ℕ}
    (h : PeriodicOn w p s e)
    (hw : ∀ q < e, w'[q]? = w[q]?) : PeriodicOn w' p s e := by sorry
