-- Prove2me | Theorems.Thm_CriticalPortraits_betaK_max
-- name    : CriticalPortraits.betaK_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:21.906682+00:00
-- url     : https://prove2.me/theorems/9c50c681-13b9-4dc8-b8cb-798605b99bc8
-- title:
--   Critical Portraits: beta K max
-- statement:
--   **Maximality (M2).** For `betaK < j ≤ lu-1`, deficiency at `j` is nonzero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L228-L233
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L228-L233

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

theorem CriticalPortraits.betaK_max {d m : ℕ} {U : Finset (ZMod (d * m))} {u : ZMod (d * m)} {j : ℕ}
    (hj1 : betaK U u < j) (hj2 : j ≤ u.val / m - 1) :
    Defc U (u.val % m) (u.val / m) u.val j ≠ 0 := by sorry
