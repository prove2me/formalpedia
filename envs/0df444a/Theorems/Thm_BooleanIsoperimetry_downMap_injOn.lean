-- Prove2me | Theorems.Thm_BooleanIsoperimetry_downMap_injOn
-- name    : BooleanIsoperimetry.downMap_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:19:46.552634+00:00
-- url     : https://prove2.me/theorems/63f53e9f-7e7e-48dd-94f5-ba428b702c29
-- title:
--   Boolean Isoperimetry: down Map inj On
-- statement:
--   The Down map is injective on its family.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L490-L506
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/SimplicialCompression.lean#L490-L506

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry

theorem BooleanIsoperimetry.downMap_injOn {N : ℕ} (i : Fin N) (A : Finset (Cube N)) :
    Set.InjOn (downMap i A) ↑A := by sorry
