-- Prove2me | Theorems.Thm_BooleanIsoperimetry_mem_layerInitSeg_iff_rank
-- name    : BooleanIsoperimetry.mem_layerInitSeg_iff_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:24:06.537254+00:00
-- url     : https://prove2.me/theorems/59ae20a2-c449-4131-9f65-4fd949e5b98d
-- title:
--   Boolean Isoperimetry: mem layer Init Seg iff rank
-- statement:
--   The Boolean Isoperimetry construction uses the mem layer Init Seg iff rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L142-L150
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/KruskalKatona.lean#L142-L150

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

theorem BooleanIsoperimetry.mem_layerInitSeg_iff_rank {N r t : ℕ} {x : Cube N} :
    x ∈ layerInitSeg N r t ↔
      x.card = r ∧ binomPrefix N r ≤ rank x ∧ rank x < binomPrefix N r + t := by sorry
