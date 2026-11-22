-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_add_le_H_add_of_ge_telescope
-- name    : BooleanIsoperimetry.H_add_le_H_add_of_ge_telescope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:55.000523+00:00
-- url     : https://prove2.me/theorems/c11459b8-f75e-41fd-9bc8-e3d876c3db8d
-- title:
--   Boolean Isoperimetry: H add le H add of ge telescope
-- statement:
--   The Boolean Isoperimetry construction uses the H add le H add of ge telescope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L784-L806
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L784-L806

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

theorem BooleanIsoperimetry.H_add_le_H_add_of_ge_telescope (n a b c d : ℕ) (hab : a + b = c + d) (hca : c ≤ a)
    (hinc : ∀ i < a - c, H (n + 1) (c + i) + H (n + 1) (d - i) ≤
      H (n + 1) (c + i + 1) + H (n + 1) (d - i - 1)) :
    H (n + 1) c + H (n + 1) d ≤ H (n + 1) a + H (n + 1) b := by sorry
