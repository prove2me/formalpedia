-- Prove2me | Theorems.Thm_CriticalPortraits_Scount_bot_le
-- name    : CriticalPortraits.Scount_bot_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:49.682332+00:00
-- url     : https://prove2.me/theorems/fc4a6cf6-fc22-4542-a625-dd814dde7941
-- title:
--   Critical Portraits: Scount bot le
-- statement:
--   The scount bound from canonicity: `#{t ∈ U : φ < t.val < u.val} ≤ lu - 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L128-L169
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L128-L169

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

theorem CriticalPortraits.Scount_bot_le {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) :
    Scount U (u.val % m) u.val ≤ u.val / m - 1 := by sorry
