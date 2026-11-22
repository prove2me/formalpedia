-- Prove2me | Theorems.Thm_BornVolume_apexMap_image_volume
-- name    : BornVolume.apexMap_image_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:30.937607+00:00
-- url     : https://prove2.me/theorems/b15c12a9-0f8c-4463-8e70-316f2cdd5c92
-- title:
--   Born Volume: apex Map image volume
-- statement:
--   The Lebesgue measure of the cell opposite the origin `0` (the last outcome) is `(1 − ∑ b)`
--   times the simplex volume, for any `b` with `∑ b ≤ 1`, including the degenerate `∑ b = 1`, where
--   the affine image is a translate of a `det = 0` linear image, hence null. (Translation
--   invariance + `Measure.addHaar_image_linearMap` + `apexLin_det`.)
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L147-L161
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L147-L161

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

theorem BornVolume.apexMap_image_volume (b : Fin M → ℝ) (hb : 0 ≤ 1 - ∑ k, b k) :
    volume ((fun x => apexLin b x + b) '' openSimplexFree)
      = ENNReal.ofReal (1 - ∑ k, b k) * volume (openSimplexFree (M := M)) := by sorry
