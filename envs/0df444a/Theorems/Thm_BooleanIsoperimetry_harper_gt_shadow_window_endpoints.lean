-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_gt_shadow_window_endpoints
-- name    : BooleanIsoperimetry.harper_gt_shadow_window_endpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:39:47.105452+00:00
-- url     : https://prove2.me/theorems/bf9e385f-3c6a-41d7-859b-07c248f249bf
-- title:
--   Boolean Isoperimetry: harper gt shadow window endpoints
-- statement:
--   The GT regime gives the left-oriented window order together with equal lengths.
--   This is the arithmetic shape of the Frankl-Füredi slack comparison: the lower
--   window `[b,q)` and the upper window `[p,a)` have common length `q-b = a-p`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L353-L359
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L353-L359

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.harper_gt_shadow_window_endpoints {n a b p q : ℕ}
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hcase : H (n + 1) b < a) :
    b ≤ q ∧ q ≤ p ∧ p ≤ a ∧ a - p = q - b := by sorry
