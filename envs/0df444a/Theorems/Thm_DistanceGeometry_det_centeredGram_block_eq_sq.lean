-- Prove2me | Theorems.Thm_DistanceGeometry_det_centeredGram_block_eq_sq
-- name    : DistanceGeometry.det_centeredGram_block_eq_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:46:08.565289+00:00
-- url     : https://prove2.me/theorems/a4695944-d9e3-4b45-b79f-1e52c71c0ff0
-- title:
--   Distance Geometry: det centered Gram block eq sq
-- statement:
--   The Gram–volume identity for `n = 2`. The determinant of the `2×2` edge-Gram block
--   of the basepoint-centered matrix `centeredGram D` (indices `{1, 2}`) equals the square of the
--   edge-coordinate determinant `det E`, where `E = [x 1 - x 0; x 2 - x 0]`. This is the
--   `n = 2` case of `det G = (n!·Vol)²` (here `det G = (2·area)²`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L216-L223
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DistanceGeometry/CayleyMengerVolume.lean#L216-L223

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

theorem DistanceGeometry.det_centeredGram_block_eq_sq
    {D : Matrix (Fin 3) (Fin 3) ℝ} {x : Fin 3 → EuclideanSpace ℝ (Fin 2)}
    (hD : IsSqDistMatrix D x) :
    centeredGram D 1 1 * centeredGram D 2 2 - (centeredGram D 1 2) ^ 2
      = ((x 1 - x 0) 0 * (x 2 - x 0) 1 - (x 1 - x 0) 1 * (x 2 - x 0) 0) ^ 2 := by sorry
