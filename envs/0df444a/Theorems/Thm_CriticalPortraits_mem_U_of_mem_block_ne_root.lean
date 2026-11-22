-- Prove2me | Theorems.Thm_CriticalPortraits_mem_U_of_mem_block_ne_root
-- name    : CriticalPortraits.mem_U_of_mem_block_ne_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:09.902804+00:00
-- url     : https://prove2.me/theorems/b9c15911-6394-4d6a-b0bd-2ca36a07266c
-- title:
--   Critical Portraits: mem U of mem block ne root
-- statement:
--   A block member that is not the root is a survivor (`∈ U`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L711-L721
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L711-L721

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

theorem CriticalPortraits.mem_U_of_mem_block_ne_root {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x y : ZMod (d * m)}
    (hy : y ∈ betaBlock U x) (hne : y ≠ betaRoot hd hm hcanon x) : y ∈ U := by sorry
