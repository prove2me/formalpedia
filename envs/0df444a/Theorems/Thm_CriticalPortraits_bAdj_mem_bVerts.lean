-- Prove2me | Theorems.Thm_CriticalPortraits_bAdj_mem_bVerts
-- name    : CriticalPortraits.bAdj_mem_bVerts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:05.61243+00:00
-- url     : https://prove2.me/theorems/28bfa112-35b4-4dc0-b265-f5f1d47d4232
-- title:
--   Critical Portraits: b Adj mem b Verts
-- statement:
--   One adjacency step from a vertex lands on a vertex.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L653-L657
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L653-L657

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

theorem CriticalPortraits.bAdj_mem_bVerts {d m : ℕ} {U : Finset (ZMod (d * m))} {x y : ZMod (d * m)}
    (h : bAdj U x y) : y ∈ bVerts U := by sorry
