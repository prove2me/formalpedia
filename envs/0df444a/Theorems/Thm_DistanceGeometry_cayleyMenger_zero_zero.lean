-- Prove2me | Theorems.Thm_DistanceGeometry_cayleyMenger_zero_zero
-- name    : DistanceGeometry.cayleyMenger_zero_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:45:57.791324+00:00
-- url     : https://prove2.me/theorems/debb6edb-030f-4f30-a872-68cefa90609a
-- title:
--   Distance Geometry: cayley Menger zero zero
-- statement:
--   The top-left entry of the Cayley–Menger matrix is `0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L77-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L77-L78

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

theorem DistanceGeometry.cayleyMenger_zero_zero (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    cayleyMenger D 0 0 = 0 := by sorry

attribute [defeq] DistanceGeometry.cayleyMenger_zero_zero
