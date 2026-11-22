-- Prove2me | Theorems.Thm_BooleanIsoperimetry_gShift_preimage_eq_insert_below_min
-- name    : BooleanIsoperimetry.gShift_preimage_eq_insert_below_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:01.841152+00:00
-- url     : https://prove2.me/theorems/b86a99d2-0169-4c88-9e10-e6350717b895
-- title:
--   Boolean Isoperimetry: g Shift preimage eq insert below min
-- statement:
--   **Exact `gShift`-preimage structure of a nonempty vertex.**
--   For a nonempty vertex `w`, the vertices `v` with `gShift v = w` are *exactly* the
--   vertices `insert j w` obtained by adding a new minimum coordinate `j` strictly
--   below `w.min'`.  (Adding such a `j` makes it the new minimum, and `gShift`
--   removes it again.)  This is the set-level Kruskal–Katona/Macaulay layer
--   structure: the `gShift`-fibre of `w` is an interval of "lower extensions".
--
--   This refines `H_increment_lower` (which only established the `⊇` inclusion and a
--   cardinality lower bound) to a full equality of fibres, and is the reusable input
--   for the exact increment-profile value `HIncrement_eq_min'`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L100-L146
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L100-L146

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

theorem BooleanIsoperimetry.gShift_preimage_eq_insert_below_min {n : ℕ} (w : Cube n) (h : w.Nonempty) :
    Finset.univ.filter (fun v : Cube n => gShift v = w)
      = (Finset.univ.filter (fun j : Fin n => (j : ℕ) < (w.min' h : ℕ))).image
          (fun j => insert j w) := by sorry
