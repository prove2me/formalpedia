-- Prove2me | Theorems.Thm_CriticalPortraits_bReach_mem_bVerts
-- name    : CriticalPortraits.bReach_mem_bVerts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:30.295107+00:00
-- url     : https://prove2.me/theorems/30bb1ffb-b940-4c80-96e9-e49cb03e0dee
-- title:
--   Critical Portraits: b Reach mem b Verts
-- statement:
--   Reachability from a vertex stays in `bVerts`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L660-L665
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L660-L665

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

theorem CriticalPortraits.bReach_mem_bVerts {d m : ℕ} {U : Finset (ZMod (d * m))} {x y : ZMod (d * m)}
    (hx : x ∈ bVerts U) (h : bReach U x y) : y ∈ bVerts U := by sorry
