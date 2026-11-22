-- Prove2me | Theorems.Thm_BornVolume_apexMap_image_measurableSet
-- name    : BornVolume.apexMap_image_measurableSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:55.094804+00:00
-- url     : https://prove2.me/theorems/01be72cb-5c86-49b6-8f53-270ffa004682
-- title:
--   Born Volume: apex Map image measurable Set
-- statement:
--   The cell opposite the origin `0` (the last outcome) is measurable, for **every** `b` (no
--   determinant hypothesis).
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L75-L78
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L75-L78

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

theorem BornVolume.apexMap_image_measurableSet (b : Fin M → ℝ) :
    MeasurableSet ((fun x => apexLin b x + b) '' openSimplexFree) := by sorry
