-- Prove2me | Theorems.Thm_BornVolume_apexLin_apply
-- name    : BornVolume.apexLin_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:21.833544+00:00
-- url     : https://prove2.me/theorems/80dcebfc-be94-4cfa-a40e-09a681ec35a5
-- title:
--   Born Volume: apex Lin apply
-- statement:
--   Coordinate formula for the apex linear part: `(apexLin b x) k = x k − (∑ x)·b k`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasurePos.lean#L113-L119
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasurePos.lean#L113-L119

module
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Definitions.Def_BornVolumeLean_Volume_VertexReplacement
public import Definitions.Def_BornVolumeLean_Volume_CellMeasurePos
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}

theorem BornVolume.apexLin_apply (b : Fin M → ℝ) (x : Fin M → ℝ) (k : Fin M) :
    (apexLin b) x k = x k - (∑ j, x j) * b k := by sorry
