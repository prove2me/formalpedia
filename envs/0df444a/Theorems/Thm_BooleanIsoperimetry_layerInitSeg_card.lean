-- Prove2me | Theorems.Thm_BooleanIsoperimetry_layerInitSeg_card
-- name    : BooleanIsoperimetry.layerInitSeg_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:05.919317+00:00
-- url     : https://prove2.me/theorems/e5c115d1-8cb3-41d7-8cdc-522ad9dd54b1
-- title:
--   Boolean Isoperimetry: layer Init Seg card
-- statement:
--   The Boolean Isoperimetry construction uses the layer Init Seg card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L89-L131
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L89-L131

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

theorem BooleanIsoperimetry.layerInitSeg_card {N r t : ℕ} (ht : t ≤ Nat.choose N r) :
    (layerInitSeg N r t).card = t := by sorry
