-- Prove2me | Theorems.Thm_CriticalPortraits_canIdx_of_canonical
-- name    : CriticalPortraits.canIdx_of_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:18.969186+00:00
-- url     : https://prove2.me/theorems/15d04ade-d51b-420a-bb41-2c99c9c4d0d7
-- title:
--   Critical Portraits: can Idx of canonical
-- statement:
--   For a canonical `(d-1)`-subset, the canonical index is `0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Denominator.lean#L552-L556
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Denominator.lean#L552-L556

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_CycleLemma
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Denominator
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
open _root_.CriticalPortraits.Cycle

theorem CriticalPortraits.canIdx_of_canonical {d m : ℕ} (hd : 0 < d) (hm : 0 < m) (c : Finset (ZMod (d * m)))
    (hcard : c.card = d - 1) (hLC : LevelCanonical d m c) : canIdx hd hm c = 0 := by sorry
