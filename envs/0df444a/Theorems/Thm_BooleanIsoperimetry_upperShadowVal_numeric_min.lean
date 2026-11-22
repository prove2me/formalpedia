-- Prove2me | Theorems.Thm_BooleanIsoperimetry_upperShadowVal_numeric_min
-- name    : BooleanIsoperimetry.upperShadowVal_numeric_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:13.67225+00:00
-- url     : https://prove2.me/theorems/452dfb8b-7e2d-4f90-8654-e144c67be683
-- title:
--   Boolean Isoperimetry: upper Shadow Val numeric min
-- statement:
--   Numeric corollary of `upperLayerShadow_min`: the numerical scaffold
--   `upperShadow` is bounded by the actual upper shadow of every same-size
--   `r`-uniform family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L481-L486
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L481-L486

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SetFamily.Shadow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Combinatorics.SetFamily.KruskalKatona
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open Finset.Colex
open BooleanIsoperimetry

theorem BooleanIsoperimetry.upperShadowVal_numeric_min {N r t : ℕ} (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose N r) {A : Finset (Cube N)}
    (hA : ∀ x ∈ A, x.card = r) (hcard : A.card = t) :
    upperShadowVal N r t ≤ (upperLayerShadow N r A).card := by sorry
