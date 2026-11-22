-- Prove2me | Theorems.Thm_BornVolume_isSigmaCompact_openSimplexFree
-- name    : BornVolume.isSigmaCompact_openSimplexFree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:10.38726+00:00
-- url     : https://prove2.me/theorems/8302e92e-3742-4d05-892b-034c4b1f3deb
-- title:
--   Born Volume: is Sigma Compact open Simplex Free
-- statement:
--   The open free simplex is σ-compact: it is an open subset of the locally
--   compact, second-countable `ℝ^M`, hence itself a locally compact second-countable
--   space, hence σ-compact (`sigmaCompactSpace_of_locallyCompact_secondCountable`).
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L51-L55
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L51-L55

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

theorem BornVolume.isSigmaCompact_openSimplexFree :
    IsSigmaCompact (openSimplexFree (M := M)) := by sorry
