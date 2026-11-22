-- Prove2me | Theorems.Thm_BornVolume_apexLin_image_isOpen
-- name    : BornVolume.apexLin_image_isOpen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:57.331989+00:00
-- url     : https://prove2.me/theorems/6f9cddab-b31d-46c0-b719-ee34d16cc38f
-- title:
--   Born Volume: apex Lin image is Open
-- statement:
--   The image of the open simplex under the `det ≠ 0` affine apex map is open.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellOpen.lean#L39-L46
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellOpen.lean#L39-L46

module
public import Definitions.Def_BornVolumeLean_Volume_CellMeasurePos
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}

theorem BornVolume.apexLin_image_isOpen (b : Fin M → ℝ) (h : LinearMap.det (apexLin b) ≠ 0) :
    IsOpen ((fun x => apexLin b x + b) '' openSimplexFree) := by sorry
