-- Prove2me | Theorems.Thm_CriticalPortraits_bridge_edge
-- name    : CriticalPortraits.bridge_edge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:15.911901+00:00
-- url     : https://prove2.me/theorems/c2e123c6-203a-461d-906e-509e32b6fe1d
-- title:
--   Critical Portraits: bridge edge
-- statement:
--   **BRIDGE (edge form).** If a survivor `b2` (same column as `u`) has its edge strictly nested
--       inside `u`'s edge, then there is a survivor `g` of a DIFFERENT column whose edge encloses
--       `b2`'s and is nested in `u`'s: `loV u ≤ loV g ≤ loV b2`, `hiV b2 ≤ hiV g ≤ hiV u`,
--       `colV g ≠ colV u`, and `g ≠ b2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L599-L634
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L599-L634

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}

theorem CriticalPortraits.bridge_edge [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P)
    {u b2 : ZMod (d * m)} (hu : u ∈ T P) (hb2 : b2 ∈ T P)
    (hcol : colV b2 = colV u)
    (hlo : loV P u < loV P b2) (hhi : hiV b2 < hiV u) :
    ∃ g ∈ T P, colV g ≠ colV u ∧
      loV P u ≤ loV P g ∧ loV P g ≤ loV P b2 ∧ hiV b2 ≤ hiV g ∧ hiV g ≤ hiV u ∧ g ≠ b2 := by sorry
