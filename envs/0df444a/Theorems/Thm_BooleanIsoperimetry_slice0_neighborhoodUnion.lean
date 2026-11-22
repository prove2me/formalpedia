-- Prove2me | Theorems.Thm_BooleanIsoperimetry_slice0_neighborhoodUnion
-- name    : BooleanIsoperimetry.slice0_neighborhoodUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:37:56.733408+00:00
-- url     : https://prove2.me/theorems/c2510cd0-2c4d-4aaf-a0e8-5c3f59f0be63
-- title:
--   Boolean Isoperimetry: slice0 neighborhood Union
-- statement:
--   The Boolean Isoperimetry construction uses the slice0 neighborhood Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2439-L2459
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L2439-L2459

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

theorem BooleanIsoperimetry.slice0_neighborhoodUnion {N x y px qx py qy : ℕ}
    (hx : CascadeSplit N x px qx) (hy : CascadeSplit N y py qy) :
    slice0 (neighborhood 1 (simplicialInitSeg (N + 1) x) ∪ simplicialInitSeg (N + 1) y)
      = neighborhood 1 (simplicialInitSeg N px) ∪ simplicialInitSeg N py := by sorry
