-- Prove2me | Theorems.Thm_BornVolume_replaceMap_image_isOpen
-- name    : BornVolume.replaceMap_image_isOpen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:27.182971+00:00
-- url     : https://prove2.me/theorems/25cd2abf-1367-4194-9cd5-926b650a7783
-- title:
--   Born Volume: replace Map image is Open
-- statement:
--   The image of the open simplex under a `det ≠ 0` vertex-replacement map is open.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellOpen.lean#L32-L36
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellOpen.lean#L32-L36

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

theorem BornVolume.replaceMap_image_isOpen (b : Fin M → ℝ) (i : Fin M)
    (h : LinearMap.det (replaceMap b i) ≠ 0) :
    IsOpen ((replaceMap b i) '' openSimplexFree) := by sorry
