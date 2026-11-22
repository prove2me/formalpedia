-- Prove2me | Theorems.Thm_BooleanIsoperimetry_hDist_eq_one_of_card_diff
-- name    : BooleanIsoperimetry.hDist_eq_one_of_card_diff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:10.783011+00:00
-- url     : https://prove2.me/theorems/3568ccad-df66-4ad6-87d2-ea750054ad16
-- title:
--   Boolean Isoperimetry: h Dist eq one of card diff
-- statement:
--   The Boolean Isoperimetry construction uses the h Dist eq one of card diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L207-L226
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L207-L226

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

theorem BooleanIsoperimetry.hDist_eq_one_of_card_diff {N r : ℕ} {u x : Cube N} (hu : u.card = r)
    (hx : x.card = r + 1) (hd : hDist u x ≤ 1) :
    u ⊆ x ∧ (x \ u).card = 1 := by sorry
