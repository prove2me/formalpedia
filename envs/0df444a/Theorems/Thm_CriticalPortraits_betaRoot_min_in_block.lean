-- Prove2me | Theorems.Thm_CriticalPortraits_betaRoot_min_in_block
-- name    : CriticalPortraits.betaRoot_min_in_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:28.386272+00:00
-- url     : https://prove2.me/theorems/e0b9788a-aade-4be8-8f4d-2c033138193a
-- title:
--   Critical Portraits: beta Root min in block
-- statement:
--   The root is `.val`-minimal in the block.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L681-L689
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L681-L689

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

theorem CriticalPortraits.betaRoot_min_in_block {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x y : ZMod (d * m)}
    (hy : y ∈ betaBlock U x) : (betaRoot hd hm hcanon x).val ≤ y.val := by sorry
