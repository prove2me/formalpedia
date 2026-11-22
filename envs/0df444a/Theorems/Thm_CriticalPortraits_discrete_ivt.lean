-- Prove2me | Theorems.Thm_CriticalPortraits_discrete_ivt
-- name    : CriticalPortraits.discrete_ivt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:01.188284+00:00
-- url     : https://prove2.me/theorems/01e17f31-855f-461c-93ea-66e9988aaae6
-- title:
--   Critical Portraits: discrete ivt
-- statement:
--   **Discrete IVT.** An integer-valued sequence with `D 0 ≤ 0`, `0 ≤ D L`, and unit-bounded
--       up-steps (`D (k+1) ≤ D k + 1`) hits zero somewhere in `[0, L]`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L65-L86
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L65-L86

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators

theorem CriticalPortraits.discrete_ivt (D : ℕ → ℤ) (L : ℕ) (h0 : D 0 ≤ 0) (hL : 0 ≤ D L)
    (hstep : ∀ k, k < L → D (k + 1) ≤ D k + 1) : ∃ k ≤ L, D k = 0 := by sorry
