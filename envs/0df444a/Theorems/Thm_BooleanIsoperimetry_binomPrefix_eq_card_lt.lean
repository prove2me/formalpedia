-- Prove2me | Theorems.Thm_BooleanIsoperimetry_binomPrefix_eq_card_lt
-- name    : BooleanIsoperimetry.binomPrefix_eq_card_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:06.602966+00:00
-- url     : https://prove2.me/theorems/a3703cc3-b87f-4c26-88ca-cd048cd853d0
-- title:
--   Boolean Isoperimetry: binom Prefix eq card lt
-- statement:
--   The Boolean Isoperimetry construction uses the binom Prefix eq card lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L64-L82
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L64-L82

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

theorem BooleanIsoperimetry.binomPrefix_eq_card_lt (N r : ℕ) :
    binomPrefix N r = (Finset.univ.filter (fun (x : Cube N) => x.card < r)).card := by sorry
