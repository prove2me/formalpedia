-- Prove2me | Theorems.Thm_BooleanIsoperimetry_toColex_lt_iff_cubeToNat_lt
-- name    : BooleanIsoperimetry.toColex_lt_iff_cubeToNat_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:20:06.753585+00:00
-- url     : https://prove2.me/theorems/b55c05a8-ef72-411b-bd91-283775702335
-- title:
--   Boolean Isoperimetry: to Colex lt iff cube To Nat lt
-- statement:
--   The Boolean Isoperimetry construction uses the to Colex lt iff cube To Nat lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L388-L403
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L388-L403

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

theorem BooleanIsoperimetry.toColex_lt_iff_cubeToNat_lt {N : ℕ} {A B : Finset (Fin N)} :
    toColex A < toColex B ↔ cubeToNat A < cubeToNat B := by sorry
