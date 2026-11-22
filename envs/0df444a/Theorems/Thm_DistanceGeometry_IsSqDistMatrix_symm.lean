-- Prove2me | Theorems.Thm_DistanceGeometry_IsSqDistMatrix_symm
-- name    : DistanceGeometry.IsSqDistMatrix.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:45:20.024589+00:00
-- url     : https://prove2.me/theorems/d4277c8c-23b3-4cec-9e1c-7d7636a341e5
-- title:
--   Is Sq Dist Matrix: symm
-- statement:
--   A squared-distance matrix is symmetric: `D i j = D j i`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L78-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L78-L81

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open scoped RealInnerProductSpace
variable {n k : ℕ}

theorem DistanceGeometry.IsSqDistMatrix.symm {D : Matrix (Fin n) (Fin n) ℝ}
    {x : Fin n → EuclideanSpace ℝ (Fin k)} (hD : IsSqDistMatrix D x) (i j : Fin n) :
    D i j = D j i := by sorry
