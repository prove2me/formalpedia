-- Prove2me | Theorems.Thm_DistanceGeometry_IsPreDistMatrix_symm
-- name    : DistanceGeometry.IsPreDistMatrix.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:45:27.692476+00:00
-- url     : https://prove2.me/theorems/d3fb6dd5-7861-43cd-89db-676d16ba62cb
-- title:
--   Is Pre Dist Matrix: symm
-- statement:
--   A matrix satisfying `IsPreDistMatrix` is symmetric.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L102-L103
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L102-L103

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open scoped RealInnerProductSpace
variable {n k : ℕ}

theorem DistanceGeometry.IsPreDistMatrix.symm {D : Matrix (Fin n) (Fin n) ℝ} (hD : IsPreDistMatrix D)
    (i j : Fin n) : D i j = D j i := by sorry
