-- Prove2me | Theorems.Thm_BooleanIsoperimetry_upShadow_eq_upperLayerShadow_of_uniform
-- name    : BooleanIsoperimetry.upShadow_eq_upperLayerShadow_of_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:15.716918+00:00
-- url     : https://prove2.me/theorems/eec67e72-b464-4a98-882b-0f5eaed37224
-- title:
--   Boolean Isoperimetry: up Shadow eq upper Layer Shadow of uniform
-- statement:
--   The Boolean Isoperimetry construction uses the up Shadow eq upper Layer Shadow of uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L338-L350
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L338-L350

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

theorem BooleanIsoperimetry.upShadow_eq_upperLayerShadow_of_uniform {N r : ℕ} {A : Finset (Cube N)}
    (hA : ∀ x ∈ A, x.card = r) :
    Finset.upShadow A = upperLayerShadow N r A := by sorry
