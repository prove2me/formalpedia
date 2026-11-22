-- Prove2me | Theorems.Thm_BornVolume_replaceMap_apply
-- name    : BornVolume.replaceMap_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:50.073838+00:00
-- url     : https://prove2.me/theorems/f95886ff-a46b-4cfc-bd54-c64c9c092594
-- title:
--   Born Volume: replace Map apply
-- statement:
--   Coordinate formula for the vertex-replacement map:
--   `(replaceMap b i t) k = b k · t i + (t k if k ≠ i else 0)`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasurePos.lean#L83-L94
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasurePos.lean#L83-L94

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

theorem BornVolume.replaceMap_apply {N : ℕ} (b : Fin N → ℝ) (i : Fin N) (t : Fin N → ℝ) (k : Fin N) :
    (replaceMap b i) t k = b k * t i + (if k = i then 0 else t k) := by sorry
