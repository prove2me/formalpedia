-- Prove2me | Theorems.Thm_BornVolume_replaceMap_image_volume
-- name    : BornVolume.replaceMap_image_volume
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:58:49.098284+00:00
-- url     : https://prove2.me/theorems/0374a24d-a904-4267-9cc2-4805946a95f1
-- title:
--   Born Volume: replace Map image volume
-- statement:
--   **The vertex-replacement map scales Lebesgue measure by `bᵢ`** (`bᵢ ≥ 0`), for every set
--   `s`. When `0 < volume s < ∞` this says `volume (replaceMap b i '' s) / volume s = bᵢ`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/VertexReplacement.lean#L58-L62
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/VertexReplacement.lean#L58-L62

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

theorem BornVolume.replaceMap_image_volume (b : Fin N → ℝ) (i : Fin N) (hb : 0 ≤ b i)
    (s : Set (Fin N → ℝ)) :
    volume (replaceMap b i '' s) = ENNReal.ofReal (b i) * volume s := by sorry
