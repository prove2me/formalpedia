-- Prove2me | Theorems.Thm_DistanceGeometry_cayleyMenger_det_segment
-- name    : DistanceGeometry.cayleyMenger_det_segment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:46:00.238067+00:00
-- url     : https://prove2.me/theorems/4114a7aa-8b29-4ea4-896c-afb6a49cfd07
-- title:
--   Distance Geometry: cayley Menger det segment
-- statement:
--   The segment case (`n = 1`) of Cayley–Menger. For two points with squared distance
--   `ℓ² = D 0 1`, the `3×3` Cayley–Menger determinant is `2·ℓ²` (the general sign is
--   `(-1)^(n+1)·2^n·det G`, here `(-1)²·2¹ = +2` and the `1×1` edge-Gram is `[ℓ²]`). With
--   `D` hollow this reads `det CM = 2 · D 0 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L133-L142
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L133-L142

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

theorem DistanceGeometry.cayleyMenger_det_segment (D : Matrix (Fin 2) (Fin 2) ℝ)
    (h00 : D 0 0 = 0) (h11 : D 1 1 = 0) (s01 : D 1 0 = D 0 1) :
    (cayleyMenger D).det = 2 * D 0 1 := by sorry
