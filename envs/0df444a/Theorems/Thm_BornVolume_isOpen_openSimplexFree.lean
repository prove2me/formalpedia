-- Prove2me | Theorems.Thm_BornVolume_isOpen_openSimplexFree
-- name    : BornVolume.isOpen_openSimplexFree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:06.660615+00:00
-- url     : https://prove2.me/theorems/c2c2ad90-5422-4802-9ee4-4a56c70952e0
-- title:
--   Born Volume: is Open open Simplex Free
-- statement:
--   The open free simplex is an open set.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasurePos.lean#L97-L102
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasurePos.lean#L97-L102

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

theorem BornVolume.isOpen_openSimplexFree {M : ℕ} : IsOpen (openSimplexFree (M := M)) := by sorry
