-- Prove2me | Theorems.Thm_CriticalPortraits_mem_bVerts_of_mem
-- name    : CriticalPortraits.mem_bVerts_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:00.976351+00:00
-- url     : https://prove2.me/theorems/85d300c7-77a7-45cc-aad1-3a387fc6a21c
-- title:
--   Critical Portraits: mem b Verts of mem
-- statement:
--   A `U`-point is a vertex.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L642-L644
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L642-L644

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

theorem CriticalPortraits.mem_bVerts_of_mem {d m : ℕ} {U : Finset (ZMod (d * m))} {x : ZMod (d * m)} (hx : x ∈ U) :
    x ∈ bVerts U := by sorry
