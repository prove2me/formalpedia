-- Prove2me | Theorems.Thm_BooleanIsoperimetry_HIncrement_window_eq_macaulayShadowWeight_sum
-- name    : BooleanIsoperimetry.HIncrement_window_eq_macaulayShadowWeight_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:12.10504+00:00
-- url     : https://prove2.me/theorems/3b74ee8c-ee3f-45c5-bfe9-3412d860838b
-- title:
--   Boolean Isoperimetry: HIncrement window eq macaulay Shadow Weight sum
-- statement:
--   Exact interval form of the Macaulay layer profile: a rank window of
--   `HIncrement` is the sum of the explicit shadow weights of the vertices whose
--   ranks lie in the same interval.  The endpoint bound `hi ≤ 2^n` is the natural
--   cube-capacity condition used by all Harper windows.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L301-L329
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L301-L329

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

theorem BooleanIsoperimetry.HIncrement_window_eq_macaulayShadowWeight_sum
    (n lo hi : ℕ) (hhi : hi ≤ 2 ^ n) :
    (∑ i ∈ Finset.Ico lo hi, HIncrement n i) =
      ∑ w ∈ (Finset.univ.filter (fun w : Cube n => lo ≤ rank w ∧ rank w < hi)),
        macaulayShadowWeight w := by sorry
