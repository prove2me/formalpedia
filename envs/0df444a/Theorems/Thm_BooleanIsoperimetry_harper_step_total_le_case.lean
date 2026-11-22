-- Prove2me | Theorems.Thm_BooleanIsoperimetry_harper_step_total_le_case
-- name    : BooleanIsoperimetry.harper_step_total_le_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:26:30.135305+00:00
-- url     : https://prove2.me/theorems/e298708c-85ee-4326-979d-4353160bd195
-- title:
--   Boolean Isoperimetry: harper step total le case
-- statement:
--   The `b ≤ a` branch of `harper_step_total`, assembled from the two max-free case
--   lemmas by collapsing the slack form of `boundaryCostH`
--   (`boundaryCostH_eq_H_add_slack`).  Sorry-free.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1450-L1463
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Harper.lean#L1450-L1463

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

theorem BooleanIsoperimetry.harper_step_total_le_case (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hba : b ≤ a) :
    H (n + 2) (a + b) ≤ boundaryCostH (n + 1) a b := by sorry
