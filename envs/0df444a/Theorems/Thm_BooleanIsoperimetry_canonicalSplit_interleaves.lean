-- Prove2me | Theorems.Thm_BooleanIsoperimetry_canonicalSplit_interleaves
-- name    : BooleanIsoperimetry.canonicalSplit_interleaves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:16:48.692837+00:00
-- url     : https://prove2.me/theorems/2eae2d86-fde1-4125-91d2-fdea51f0c29a
-- title:
--   Boolean Isoperimetry: canonical Split interleaves
-- statement:
--   The canonical cascade split of `a + b` maximizes prefix mass, hence interleaves
--   any other split `(a, b)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L1027-L1035
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L1027-L1035

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

theorem BooleanIsoperimetry.canonicalSplit_interleaves
    {n a b p q : ℕ} (_ha : a ≤ 2 ^ n) (_hb : b ≤ 2 ^ n)
    (h_casc : CascadeSplit n (a + b) p q) :
    CascadeInterleaves n p q a b := by sorry
