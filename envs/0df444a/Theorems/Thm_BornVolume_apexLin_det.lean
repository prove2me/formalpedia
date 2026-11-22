-- Prove2me | Theorems.Thm_BornVolume_apexLin_det
-- name    : BornVolume.apexLin_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:01.306115+00:00
-- url     : https://prove2.me/theorems/6f220627-42a6-4878-a942-7199ac706fbb
-- title:
--   Born Volume: apex Lin det
-- statement:
--   `det (apexLin b) = 1 − ∑ b` (matrix determinant lemma via `det_one_sub_mul_comm`).
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasurePos.lean#L122-L129
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasurePos.lean#L122-L129

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

theorem BornVolume.apexLin_det (b : Fin M → ℝ) : LinearMap.det (apexLin b) = 1 - ∑ k, b k := by sorry
