-- Prove2me | Theorems.Thm_DistanceGeometry_IsSqDistMatrix_isPreDistMatrix
-- name    : DistanceGeometry.IsSqDistMatrix.isPreDistMatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:45:30.932844+00:00
-- url     : https://prove2.me/theorems/8e4bcd86-2dc7-47ce-b828-6d5f2982f9a7
-- title:
--   Is Sq Dist Matrix: is Pre Dist Matrix
-- statement:
--   Every squared-distance matrix satisfies `IsPreDistMatrix`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L110-L113
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L110-L113

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open scoped RealInnerProductSpace
variable {n k : ℕ}

theorem DistanceGeometry.IsSqDistMatrix.isPreDistMatrix {D : Matrix (Fin n) (Fin n) ℝ}
    {x : Fin n → EuclideanSpace ℝ (Fin k)} (hD : IsSqDistMatrix D x) :
    IsPreDistMatrix D := by sorry
