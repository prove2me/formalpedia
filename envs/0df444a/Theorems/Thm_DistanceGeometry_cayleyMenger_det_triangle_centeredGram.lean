-- Prove2me | Theorems.Thm_DistanceGeometry_cayleyMenger_det_triangle_centeredGram
-- name    : DistanceGeometry.cayleyMenger_det_triangle_centeredGram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:46:01.021962+00:00
-- url     : https://prove2.me/theorems/fafa68fe-b28a-4ca5-8573-c333d21d184e
-- title:
--   Distance Geometry: cayley Menger det triangle centered Gram
-- statement:
--   The triangle Cayley–Menger determinant in terms of the basepoint-centered
--   matrix `centeredGram`. The `2×2` edge-Gram block above is exactly `centeredGram D`
--   restricted to the nonzero
--   indices `{1, 2}` (cf. `Defs.centeredGram`): its diagonal entries are
--   `centeredGram D 1 1 = D 0 1`, `centeredGram D 2 2 = D 0 2` (by hollowness) and its
--   off-diagonal is `centeredGram D 1 2`. Hence
--
--   `det CM = -4 · (centeredGram D 1 1 · centeredGram D 2 2 - (centeredGram D 1 2)²)`.
--
--   This is the bridge from the Cayley–Menger determinant to the Schoenberg core.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L182-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L182-L192

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

theorem DistanceGeometry.cayleyMenger_det_triangle_centeredGram (D : Matrix (Fin 3) (Fin 3) ℝ)
    (h00 : D 0 0 = 0) (h11 : D 1 1 = 0) (h22 : D 2 2 = 0)
    (s01 : D 1 0 = D 0 1) (s02 : D 2 0 = D 0 2) (s12 : D 2 1 = D 1 2) :
    (cayleyMenger D).det
      = -4 * (centeredGram D 1 1 * centeredGram D 2 2 - (centeredGram D 1 2) ^ 2) := by sorry
