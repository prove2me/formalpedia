-- Prove2me | Theorems.Thm_CriticalPortraits_minVal_betaBlock
-- name    : CriticalPortraits.minVal_betaBlock
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:32.941991+00:00
-- url     : https://prove2.me/theorems/e013ace8-c1fd-4bda-beed-50bba2545db2
-- title:
--   Critical Portraits: min Val beta Block
-- statement:
--   The minimum of a block is its root.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L697-L708
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L697-L708

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

theorem CriticalPortraits.minVal_betaBlock {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x : ZMod (d * m)}
    (hx : x ∈ bVerts U) :
    minVal (betaBlock U x) (betaBlock_nonempty hx) = betaRoot hd hm hcanon x := by sorry
