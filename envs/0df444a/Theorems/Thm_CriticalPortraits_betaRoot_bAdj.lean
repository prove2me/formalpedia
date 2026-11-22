-- Prove2me | Theorems.Thm_CriticalPortraits_betaRoot_bAdj
-- name    : CriticalPortraits.betaRoot_bAdj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:06.055212+00:00
-- url     : https://prove2.me/theorems/28cad4c8-c304-43ce-a982-affe36bf3e17
-- title:
--   Critical Portraits: beta Root b Adj
-- statement:
--   The root is invariant under one adjacency step.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L621-L628
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L621-L628

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

theorem CriticalPortraits.betaRoot_bAdj {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x y : ZMod (d * m)}
    (h : bAdj U x y) : betaRoot hd hm hcanon x = betaRoot hd hm hcanon y := by sorry
