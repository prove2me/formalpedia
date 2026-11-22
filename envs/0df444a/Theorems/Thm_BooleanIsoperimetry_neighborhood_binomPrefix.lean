-- Prove2me | Theorems.Thm_BooleanIsoperimetry_neighborhood_binomPrefix
-- name    : BooleanIsoperimetry.neighborhood_binomPrefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:05.634216+00:00
-- url     : https://prove2.me/theorems/2eb27939-a029-4c47-8a59-19fbb8885b6e
-- title:
--   Boolean Isoperimetry: neighborhood binom Prefix
-- statement:
--   The Boolean Isoperimetry construction uses the neighborhood binom Prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L137-L140
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L137-L140

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

theorem BooleanIsoperimetry.neighborhood_binomPrefix {N r : ℕ} (hr : 1 ≤ r) :
    neighborhood 1 (simplicialInitSeg N (binomPrefix N r)) =
    simplicialInitSeg N (binomPrefix N (r + 1)) := by sorry
