-- Prove2me | Theorems.Thm_CriticalPortraits_betaBlock_mem_beta
-- name    : CriticalPortraits.betaBlock_mem_beta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:09.760479+00:00
-- url     : https://prove2.me/theorems/9dee9dad-8deb-4502-b846-5503ee1da6b3
-- title:
--   Critical Portraits: beta Block mem beta
-- statement:
--   `betaBlock U x ∈ beta U` for a vertex `x`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L724-L726
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L724-L726

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
variable {d m : ℕ}

theorem CriticalPortraits.betaBlock_mem_beta {d m : ℕ} {U : Finset (ZMod (d * m))} {x : ZMod (d * m)}
    (hx : x ∈ bVerts U) : betaBlock U x ∈ beta U := by sorry
