-- Prove2me | Theorems.Thm_BornVolume_volume_openSimplexFree
-- name    : BornVolume.volume_openSimplexFree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:03:58.873454+00:00
-- url     : https://prove2.me/theorems/2d409017-b41a-4807-afcd-7272da2d330b
-- title:
--   Born Volume: volume open Simplex Free
-- statement:
--   **The open simplex has volume `(M!)⁻¹`.** Forced by `μ_FS` being a
--   probability measure: pushing it forward gives `M! · vol|_{openSimplexFree}`, whose total
--   mass is `1`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasurePos.lean#L58-L77
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasurePos.lean#L58-L77

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

theorem BornVolume.volume_openSimplexFree :
    volume (openSimplexFree (M := M)) = (Nat.factorial M : ℝ≥0∞)⁻¹ := by sorry
