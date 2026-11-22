-- Prove2me | Theorems.Thm_BornVolume_euclidean_norm_sq_eq_sum
-- name    : BornVolume.euclidean_norm_sq_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:20.784004+00:00
-- url     : https://prove2.me/theorems/865ccbab-1854-4fc2-afb6-c3f4962c6429
-- title:
--   Born Volume: euclidean norm sq eq sum
-- statement:
--   `‖v‖² = ∑ᵢ ‖vᵢ‖²` on Euclidean space. An alias for `EuclideanSpace.norm_sq_eq`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentMap.lean#L28-L30
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentMap.lean#L28-L30

module
public import Definitions.Def_BornVolumeLean_Volume_CPN
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MomentMap
public import Definitions.Def_BornVolumeLean_Volume_MomentMap
set_option autoImplicit false
@[expose] public section
public section
open scoped LinearAlgebra.Projectivization
open BornVolume

theorem BornVolume.euclidean_norm_sq_eq_sum {N : ℕ} (v : EuclideanSpace ℂ (Fin N)) :
    ‖v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by sorry
