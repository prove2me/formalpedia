-- Prove2me | Theorems.Thm_BooleanIsoperimetry_H_increment_eq_gShift_inv
-- name    : BooleanIsoperimetry.H_increment_eq_gShift_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:00.38019+00:00
-- url     : https://prove2.me/theorems/3334e558-8c39-41d0-89d7-56e6e46888aa
-- title:
--   Boolean Isoperimetry: H increment eq g Shift inv
-- statement:
--   The exact increment of `H`: passing from an initial segment of size `p` to `p + 1`
--   enlarges the closed neighbourhood by exactly the number of vertices whose `gShift`
--   is the unique rank-`p` vertex `w`.
--
--   This provides the exact layer-profile increment structure for `H`, upgrading the
--   lower bound in `H_increment_lower` to a full structural equality.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L758-L785
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L758-L785

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem BooleanIsoperimetry.H_increment_eq_gShift_inv (n p : ℕ) (w : Cube n) (hw : rank w = p) :
    H n (p + 1) =
      H n p + (Finset.filter (fun v => gShift v = w) (Finset.univ : Finset (Cube n))).card := by sorry
