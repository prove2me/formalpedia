-- Prove2me | Theorems.Thm_BooleanIsoperimetry_card_filter_neighborhoodUnion_initSeg
-- name    : BooleanIsoperimetry.card_filter_neighborhoodUnion_initSeg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:12.639798+00:00
-- url     : https://prove2.me/theorems/2dd2c8bc-faf5-4f84-970d-3e4d627f0b72
-- title:
--   Boolean Isoperimetry: card filter neighborhood Union init Seg
-- statement:
--   The Boolean Isoperimetry construction uses the card filter neighborhood Union init Seg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2471-L2476
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2471-L2476

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry

theorem BooleanIsoperimetry.card_filter_neighborhoodUnion_initSeg (N x y k : ℕ) (hy : y ≤ 2 ^ N) :
    ((neighborhood 1 (simplicialInitSeg N x) ∪ simplicialInitSeg N y).filter
          (fun z => k ≤ z.card)).card
    = max (H N x) y - binomPrefix N k := by sorry
