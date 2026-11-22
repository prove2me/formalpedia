-- Prove2me | Theorems.Thm_BornVolume_measurable_ratio_momentMap
-- name    : BornVolume.measurable_ratio_momentMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:03.695902+00:00
-- url     : https://prove2.me/theorems/902ac8c2-5ff1-4322-89c1-d01254644460
-- title:
--   Born Volume: measurable ratio moment Map
-- statement:
--   The free-coordinate moment map `p ↦ ratioN (momentMap p)` is measurable.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasurePos.lean#L34-L41
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasurePos.lean#L34-L41

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

theorem BornVolume.measurable_ratio_momentMap :
    Measurable (fun p : CPN (M + 1) => ratioN (fun i => momentMap p i)) := by sorry
