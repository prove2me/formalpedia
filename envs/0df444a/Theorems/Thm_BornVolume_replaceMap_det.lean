-- Prove2me | Theorems.Thm_BornVolume_replaceMap_det
-- name    : BornVolume.replaceMap_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:53.531902+00:00
-- url     : https://prove2.me/theorems/2cf85470-65ea-4cc8-8677-c47bf9f57c3f
-- title:
--   Born Volume: replace Map det
-- statement:
--   The determinant of the vertex-replacement map is `bᵢ` (Cramer's rule on the identity).
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/VertexReplacement.lean#L51-L54
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/VertexReplacement.lean#L51-L54

module
public import Definitions.Def_BornVolumeLean_Volume_MomentMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Definitions.Def_BornVolumeLean_Volume_VertexReplacement
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Matrix
open scoped LinearAlgebra.Projectivization
open BornVolume
variable {N : ℕ}

theorem BornVolume.replaceMap_det (b : Fin N → ℝ) (i : Fin N) :
    LinearMap.det (replaceMap b i) = b i := by sorry
