-- Prove2me | Theorems.Thm_DeciSigma1_Words_PeriodicOn_union
-- name    : DeciSigma1.Words.PeriodicOn.union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:13.599323+00:00
-- url     : https://prove2.me/theorems/c0f38064-7043-44e2-a2b0-45df44445923
-- title:
--   Periodic On: union
-- statement:
--   Two intervals with period `d` that overlap in at least `d` positions form one interval with
--   period `d`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L183-L188
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Periods.lean#L183-L188

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

theorem DeciSigma1.Words.PeriodicOn.union {s₂ e₂ : ℕ} (h₁ : PeriodicOn w d s e) (h₂ : PeriodicOn w d s₂ e₂)
    (hov : s₂ + d ≤ e) : PeriodicOn w d s (max e e₂) := by sorry
