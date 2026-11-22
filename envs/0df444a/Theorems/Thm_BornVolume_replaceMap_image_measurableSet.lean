-- Prove2me | Theorems.Thm_BornVolume_replaceMap_image_measurableSet
-- name    : BornVolume.replaceMap_image_measurableSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:54.91084+00:00
-- url     : https://prove2.me/theorems/db5336b7-38e0-4041-98eb-807b5fc89639
-- title:
--   Born Volume: replace Map image measurable Set
-- statement:
--   The `i`-th cell is measurable, for **every** `b` (no
--   determinant hypothesis).
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L69-L71
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L69-L71

module
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}

theorem BornVolume.replaceMap_image_measurableSet (b : Fin M → ℝ) (i : Fin M) :
    MeasurableSet ((replaceMap b i) '' openSimplexFree) := by sorry
