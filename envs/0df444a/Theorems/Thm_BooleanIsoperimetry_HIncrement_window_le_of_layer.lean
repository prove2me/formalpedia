-- Prove2me | Theorems.Thm_BooleanIsoperimetry_HIncrement_window_le_of_layer
-- name    : BooleanIsoperimetry.HIncrement_window_le_of_layer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:10.351311+00:00
-- url     : https://prove2.me/theorems/9fb85742-396d-48fd-8484-33adcb925642
-- title:
--   Boolean Isoperimetry: HIncrement window le of layer
-- statement:
--   **Per-layer increment window bound.**  A length-`L` rank window contained in a
--   single Macaulay layer `r` has total `HIncrement` mass at most `L * (n - r)`.  This
--   is the reusable upper-shadow-window bound for a window confined to one layer; it
--   follows by summing `HIncrement_le_of_mem_layer` over the window.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L284-L293
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L284-L293

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.HIncrement_window_le_of_layer {n r a L : ℕ} (hr : 1 ≤ r)
    (hlo : binomPrefix n r ≤ a) (hhi : a + L ≤ binomPrefix n (r + 1)) :
    (∑ i ∈ Finset.Ico a (a + L), HIncrement n i) ≤ L * (n - r) := by sorry
