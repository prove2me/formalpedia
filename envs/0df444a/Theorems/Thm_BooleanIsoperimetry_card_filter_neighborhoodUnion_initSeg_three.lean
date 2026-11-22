-- Prove2me | Theorems.Thm_BooleanIsoperimetry_card_filter_neighborhoodUnion_initSeg_three
-- name    : BooleanIsoperimetry.card_filter_neighborhoodUnion_initSeg_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:18.39136+00:00
-- url     : https://prove2.me/theorems/6c13f921-8d65-4f56-b194-c62774052921
-- title:
--   Boolean Isoperimetry: card filter neighborhood Union init Seg three
-- statement:
--   The Boolean Isoperimetry construction uses the card filter neighborhood Union init Seg three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2478-L2491
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2478-L2491

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

theorem BooleanIsoperimetry.card_filter_neighborhoodUnion_initSeg_three (N x y z k : ℕ)
    (h_le : H N x ≤ y) (hy : y ≤ 2 ^ N) (hz : z ≤ 2 ^ N) :
    ((neighborhood 1 (simplicialInitSeg N x) ∪ simplicialInitSeg N y ∪ simplicialInitSeg N z).filter
          (fun z => k ≤ z.card)).card
    = max y z - binomPrefix N k := by sorry
