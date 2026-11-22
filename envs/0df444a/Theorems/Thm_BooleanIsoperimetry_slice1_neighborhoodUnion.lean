-- Prove2me | Theorems.Thm_BooleanIsoperimetry_slice1_neighborhoodUnion
-- name    : BooleanIsoperimetry.slice1_neighborhoodUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:38:07.781059+00:00
-- url     : https://prove2.me/theorems/c66c76c2-c23d-4946-b977-5c3ceb2fe33d
-- title:
--   Boolean Isoperimetry: slice1 neighborhood Union
-- statement:
--   The Boolean Isoperimetry construction uses the slice1 neighborhood Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2461-L2469
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2461-L2469

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

theorem BooleanIsoperimetry.slice1_neighborhoodUnion {N x y px qx py qy : ℕ}
    (hx : CascadeSplit N x px qx) (hy : CascadeSplit N y py qy) :
    slice1 (neighborhood 1 (simplicialInitSeg (N + 1) x) ∪ simplicialInitSeg (N + 1) y)
      = neighborhood 1 (simplicialInitSeg N qx) ∪ simplicialInitSeg N px ∪
          simplicialInitSeg N qy := by sorry
