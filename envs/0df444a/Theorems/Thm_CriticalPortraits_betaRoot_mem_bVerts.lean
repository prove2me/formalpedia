-- Prove2me | Theorems.Thm_CriticalPortraits_betaRoot_mem_bVerts
-- name    : CriticalPortraits.betaRoot_mem_bVerts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:09.912046+00:00
-- url     : https://prove2.me/theorems/def62e33-a65d-43d8-848d-1fa1e4bc7476
-- title:
--   Critical Portraits: beta Root mem b Verts
-- statement:
--   The root of a vertex is a vertex.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L668-L671
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L668-L671

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

theorem CriticalPortraits.betaRoot_mem_bVerts {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x : ZMod (d * m)}
    (hx : x ∈ bVerts U) : betaRoot hd hm hcanon x ∈ bVerts U := by sorry
