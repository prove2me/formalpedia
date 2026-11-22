-- Prove2me | Theorems.Thm_CriticalPortraits_betaBlock_two_le
-- name    : CriticalPortraits.betaBlock_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:13.322715+00:00
-- url     : https://prove2.me/theorems/b09d8506-50e2-49af-9ad5-4fbbe63d1cde
-- title:
--   Critical Portraits: beta Block two le
-- statement:
--   Every block contains a second point besides its root (its root has a `U`-child, or the
--       vertex itself is a `U`-point).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L779-L830
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L779-L830

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

theorem CriticalPortraits.betaBlock_two_le {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {v : ZMod (d * m)}
    (hv : v ∈ bVerts U) : 2 ≤ (betaBlock U v).card := by sorry
