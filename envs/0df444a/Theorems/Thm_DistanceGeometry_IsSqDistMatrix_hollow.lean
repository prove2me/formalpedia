-- Prove2me | Theorems.Thm_DistanceGeometry_IsSqDistMatrix_hollow
-- name    : DistanceGeometry.IsSqDistMatrix.hollow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:45:22.659894+00:00
-- url     : https://prove2.me/theorems/34a328e3-6594-4ae5-b4db-50a4e272e67f
-- title:
--   Is Sq Dist Matrix: hollow
-- statement:
--   A squared-distance matrix is hollow: its diagonal vanishes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L84-L87
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L84-L87

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open scoped RealInnerProductSpace
variable {n k : ℕ}

theorem DistanceGeometry.IsSqDistMatrix.hollow {D : Matrix (Fin n) (Fin n) ℝ}
    {x : Fin n → EuclideanSpace ℝ (Fin k)} (hD : IsSqDistMatrix D x) (i : Fin n) :
    D i i = 0 := by sorry
