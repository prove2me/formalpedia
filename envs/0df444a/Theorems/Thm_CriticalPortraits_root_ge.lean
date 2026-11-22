-- Prove2me | Theorems.Thm_CriticalPortraits_root_ge
-- name    : CriticalPortraits.root_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:25.926903+00:00
-- url     : https://prove2.me/theorems/0de4233b-50b9-4fc1-9397-e4f438b1195a
-- title:
--   Critical Portraits: root ge
-- statement:
--   The **root stays above the edge bottom**: for an edge `(v,u)` and any vertex `w` strictly
--       inside its val-interval, the root of `w` has val `≥ v`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L1284-L1316
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L1284-L1316

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

theorem CriticalPortraits.root_ge {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) :
    ∀ w : ZMod (d*m), w ∈ bVerts U →
      (betaParent U u).val < w.val → w.val < u.val →
      (betaParent U u).val ≤ (betaRoot hd hm hcanon w).val := by sorry
