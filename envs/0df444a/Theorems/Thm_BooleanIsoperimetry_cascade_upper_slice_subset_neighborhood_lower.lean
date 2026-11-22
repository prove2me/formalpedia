-- Prove2me | Theorems.Thm_BooleanIsoperimetry_cascade_upper_slice_subset_neighborhood_lower
-- name    : BooleanIsoperimetry.cascade_upper_slice_subset_neighborhood_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:45.385249+00:00
-- url     : https://prove2.me/theorems/5e6743eb-fef2-40e5-93dc-ec73deddf4d0
-- title:
--   Boolean Isoperimetry: cascade upper slice subset neighborhood lower
-- statement:
--   The Boolean Isoperimetry construction uses the cascade upper slice subset neighborhood lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2430-L2437
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2430-L2437

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

theorem BooleanIsoperimetry.cascade_upper_slice_subset_neighborhood_lower {N x p q : ℕ}
    (h : CascadeSplit N x p q) :
    simplicialInitSeg N q ⊆ neighborhood 1 (simplicialInitSeg N p) := by sorry
