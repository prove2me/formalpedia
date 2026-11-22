-- Prove2me | Theorems.Thm_DistanceGeometry_IsPreDistMatrix_hollow
-- name    : DistanceGeometry.IsPreDistMatrix.hollow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:45:24.64566+00:00
-- url     : https://prove2.me/theorems/46c0b6da-3b48-4fab-b898-a131709b71e1
-- title:
--   Is Pre Dist Matrix: hollow
-- statement:
--   A matrix satisfying `IsPreDistMatrix` is hollow.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L106-L107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/Defs.lean#L106-L107

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open scoped RealInnerProductSpace
variable {n k : ℕ}

theorem DistanceGeometry.IsPreDistMatrix.hollow {D : Matrix (Fin n) (Fin n) ℝ} (hD : IsPreDistMatrix D)
    (i : Fin n) : D i i = 0 := by sorry
