-- Prove2me | Theorems.Thm_BooleanIsoperimetry_HIncrement_eq_gShift_inv
-- name    : BooleanIsoperimetry.HIncrement_eq_gShift_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:00.596714+00:00
-- url     : https://prove2.me/theorems/76cd2037-427d-4535-83be-40a4e4459733
-- title:
--   Boolean Isoperimetry: HIncrement eq g Shift inv
-- statement:
--   The exact first difference of `H` is the number of preimages of the rank-`p` vertex
--   under `gShift`. This exactly captures the Kruskal-Katona binomial layer profile.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L82-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L82-L87

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

theorem BooleanIsoperimetry.HIncrement_eq_gShift_inv (n p : ℕ) (w : Cube n) (hw : rank w = p) :
    HIncrement n p =
      (Finset.filter (fun v => gShift v = w) (Finset.univ : Finset (Cube n))).card := by sorry
