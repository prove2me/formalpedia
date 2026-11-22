-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cubeToNat_compl_lt_cubeToNat_compl
-- name    : BooleanIsoperimetry.cubeToNat_compl_lt_cubeToNat_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:18.761852+00:00
-- url     : https://prove2.me/theorems/b91e5128-10ea-4b58-b819-9d38631ccd81
-- title:
--   Boolean Isoperimetry: cube To Nat compl lt cube To Nat compl
-- statement:
--   The Boolean Isoperimetry construction uses the cube To Nat compl lt cube To Nat compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L382-L386
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L382-L386

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

theorem BooleanIsoperimetry.cubeToNat_compl_lt_cubeToNat_compl {N : ℕ} {A B : Finset (Fin N)} :
    cubeToNat Aᶜ < cubeToNat Bᶜ ↔ cubeToNat B < cubeToNat A := by sorry
