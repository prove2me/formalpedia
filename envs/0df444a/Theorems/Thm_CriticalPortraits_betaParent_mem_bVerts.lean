-- Prove2me | Theorems.Thm_CriticalPortraits_betaParent_mem_bVerts
-- name    : CriticalPortraits.betaParent_mem_bVerts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:56.252101+00:00
-- url     : https://prove2.me/theorems/576440a5-4f8b-4bb5-b7b9-72ac22db8b78
-- title:
--   Critical Portraits: beta Parent mem b Verts
-- statement:
--   A balance parent of a `U`-point is a vertex.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L647-L650
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L647-L650

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

theorem CriticalPortraits.betaParent_mem_bVerts {d m : ℕ} {U : Finset (ZMod (d * m))} {u : ZMod (d * m)} (hu : u ∈ U) :
    betaParent U u ∈ bVerts U := by sorry
