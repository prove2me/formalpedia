-- Prove2me | Theorems.Thm_CriticalPortraits_descend_cross
-- name    : CriticalPortraits.descend_cross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:31.872616+00:00
-- url     : https://prove2.me/theorems/1c6088e1-7182-460c-b4fa-3fdb9296322f
-- title:
--   Critical Portraits: descend cross
-- statement:
--   **Descend across a threshold.** If `w` is a vertex with `betaRoot w ≤ L < w.val`,
--       then descending
--       the parent chain crosses `L`: some survivor `b` reachable from `w` has
--       `v*(b).val ≤ L < b.val`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L1322-L1349
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L1322-L1349

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

theorem CriticalPortraits.descend_cross {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) (L : ℕ) :
    ∀ w : ZMod (d*m), (betaRoot hd hm hcanon w).val ≤ L → L < w.val →
      ∃ b : ZMod (d*m), b ∈ U ∧ bReach U w b ∧ (betaParent U b).val ≤ L ∧ L < b.val := by sorry
