-- Prove2me | Theorems.Thm_BooleanIsoperimetry_slice1_eq_filter
-- name    : BooleanIsoperimetry.slice1_eq_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:51.670917+00:00
-- url     : https://prove2.me/theorems/9474ea3c-3e6e-4c95-9adb-ad71cac25505
-- title:
--   Boolean Isoperimetry: slice1 eq filter
-- statement:
--   The upper slice of an initial segment as an explicit filter.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L402-L408
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Cascade.lean#L402-L408

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

theorem BooleanIsoperimetry.slice1_eq_filter {n k : ℕ} :
    slice1 (simplicialInitSeg (n + 1) k)
      = Finset.univ.filter
          (fun w : Cube n => rank w + binomPrefix n (w.card + 1) < k) := by sorry
