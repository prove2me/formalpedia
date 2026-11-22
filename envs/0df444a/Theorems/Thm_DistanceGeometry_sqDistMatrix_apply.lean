-- Prove2me | Theorems.Thm_DistanceGeometry_sqDistMatrix_apply
-- name    : DistanceGeometry.sqDistMatrix_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:45:21.165853+00:00
-- url     : https://prove2.me/theorems/f297bd0c-6ec8-4290-a419-bcf171bd73fc
-- title:
--   Distance Geometry: sq Dist Matrix apply
-- statement:
--   The Distance Geometry construction uses the sq Dist Matrix apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L63-L64
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L63-L64

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open scoped RealInnerProductSpace
variable {n k : ℕ}

theorem DistanceGeometry.sqDistMatrix_apply (x : Fin n → EuclideanSpace ℝ (Fin k)) (i j : Fin n) :
    sqDistMatrix x i j = dist (x i) (x j) ^ 2 := by sorry

attribute [defeq] DistanceGeometry.sqDistMatrix_apply
