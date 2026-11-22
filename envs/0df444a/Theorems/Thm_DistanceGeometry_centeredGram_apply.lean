-- Prove2me | Theorems.Thm_DistanceGeometry_centeredGram_apply
-- name    : DistanceGeometry.centeredGram_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:45:22.481667+00:00
-- url     : https://prove2.me/theorems/6eade526-46ae-4b02-989d-31a200d0e276
-- title:
--   Distance Geometry: centered Gram apply
-- statement:
--   The Distance Geometry construction uses the centered Gram apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L125-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L125-L126

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open scoped RealInnerProductSpace
variable {n k : ℕ}

theorem DistanceGeometry.centeredGram_apply [NeZero n] (D : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    centeredGram D i j = (D 0 i + D 0 j - D i j) / 2 := by sorry

attribute [defeq] DistanceGeometry.centeredGram_apply
