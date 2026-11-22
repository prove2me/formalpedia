-- Prove2me | Theorems.Thm_DistanceGeometry_cayleyMenger_det_heron
-- name    : DistanceGeometry.cayleyMenger_det_heron
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:46:02.608202+00:00
-- url     : https://prove2.me/theorems/32d3f628-09ec-4c6c-84e8-3b5af38b5cc5
-- title:
--   Distance Geometry: cayley Menger det heron
-- statement:
--   The Cayley–Menger triangle-area identity (`n = 2`). For a triangle on three points
--   `x` of the Euclidean plane with squared-distance matrix `D`, the `4×4`
--   Cayley–Menger determinant equals `-16` times the squared area:
--
--   `det CM = -16 · area²`.
--
--   After expansion and factorization in the three side lengths, this identity is equivalent
--   to Heron's formula `16·area² = (a+b+c)(-a+b+c)(a-b+c)(a+b-c)`. This file does not
--   state that factorized formula as a separate theorem.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L234-L242
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L234-L242

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

theorem DistanceGeometry.cayleyMenger_det_heron
    {D : Matrix (Fin 3) (Fin 3) ℝ} {x : Fin 3 → EuclideanSpace ℝ (Fin 2)}
    (hD : IsSqDistMatrix D x) :
    (cayleyMenger D).det = -16 * (triangleArea x) ^ 2 := by sorry
