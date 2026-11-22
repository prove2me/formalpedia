-- Prove2me | Theorems.Thm_DistanceGeometry_cayleyMenger_det_triangle
-- name    : DistanceGeometry.cayleyMenger_det_triangle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:45:58.560963+00:00
-- url     : https://prove2.me/theorems/96ddaf1b-8dbc-4e54-adf7-b894a8443bfd
-- title:
--   Distance Geometry: cayley Menger det triangle
-- statement:
--   The triangle case (`n = 2`) of Cayley–Menger, algebraic form. For three points
--   with a symmetric hollow squared-distance matrix `D`, the `4×4` Cayley–Menger
--   determinant equals `-4` times the determinant of the `2×2` edge-Gram block
--
--   `G = [[D 0 1, (D 0 1 + D 0 2 - D 1 2)/2],`
--   `     [(D 0 1 + D 0 2 - D 1 2)/2, D 0 2]]`
--
--   i.e. `det CM = -4 · (D 0 1 · D 0 2 - ((D 0 1 + D 0 2 - D 1 2)/2)²)`. This is a pure
--   algebraic identity in the entries of `D`; no geometry is used.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L155-L170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L155-L170

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

theorem DistanceGeometry.cayleyMenger_det_triangle (D : Matrix (Fin 3) (Fin 3) ℝ)
    (h00 : D 0 0 = 0) (h11 : D 1 1 = 0) (h22 : D 2 2 = 0)
    (s01 : D 1 0 = D 0 1) (s02 : D 2 0 = D 0 2) (s12 : D 2 1 = D 1 2) :
    (cayleyMenger D).det
      = -4 * (D 0 1 * D 0 2 - ((D 0 1 + D 0 2 - D 1 2) / 2) ^ 2) := by sorry
