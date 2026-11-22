-- Prove2me | Theorems.Thm_BooleanIsoperimetry_upperShadow_numeric_min
-- name    : BooleanIsoperimetry.upperShadow_numeric_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:40:52.258414+00:00
-- url     : https://prove2.me/theorems/24ecb7f7-399e-4c7d-98d4-3ffb9c78254e
-- title:
--   Boolean Isoperimetry: upper Shadow numeric min
-- statement:
--   `Shadow.upperShadow` form of the Kruskal–Katona numeric minimum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SetFamilyShadow.lean#L54-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SetFamilyShadow.lean#L54-L59

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SetFamilyShadow
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry

theorem BooleanIsoperimetry.upperShadow_numeric_min {N r t : ℕ} (hr : 1 ≤ r)
    (ht : t ≤ Nat.choose N r) {A : Finset (Cube N)}
    (hA : ∀ x ∈ A, x.card = r) (hcard : A.card = t) :
    upperShadow N r t ≤ (upperLayerShadow N r A).card := by sorry
