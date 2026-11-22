-- Prove2me | Theorems.Thm_DistanceGeometry_cayleyMenger_succ_zero
-- name    : DistanceGeometry.cayleyMenger_succ_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:46:03.610188+00:00
-- url     : https://prove2.me/theorems/fe33f705-c993-4b28-a79b-68d2136c32f3
-- title:
--   Distance Geometry: cayley Menger succ zero
-- statement:
--   Off the corner, the first column of the Cayley–Menger matrix is all `1`s.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L85-L86
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L85-L86

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Definitions.Def_LeanPool_DistanceGeometry_CayleyMengerVolume
set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open Matrix
open scoped RealInnerProductSpace
variable {n : ℕ}

theorem DistanceGeometry.cayleyMenger_succ_zero (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i : Fin (n + 1)) : cayleyMenger D i.succ 0 = 1 := by sorry

attribute [defeq] DistanceGeometry.cayleyMenger_succ_zero
