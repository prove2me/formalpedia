-- Prove2me | Theorems.Thm_BornVolume_replaceMap_image_subset_of_closedSimplex
-- name    : BornVolume.replaceMap_image_subset_of_closedSimplex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:26.128943+00:00
-- url     : https://prove2.me/theorems/07e04cae-96ed-46ca-9fab-b495c2ec0240
-- title:
--   Born Volume: replace Map image subset of closed Simplex
-- statement:
--   **The `i`-th cell lies in the open simplex**, assuming only `0 ≤ b`, `∑ b ≤ 1`, and
--   `0 < b i` (the only coordinate whose strict positivity the `k = i` coordinate of the image
--   needs).
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L97-L120
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L97-L120

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

theorem BornVolume.replaceMap_image_subset_of_closedSimplex (b : Fin M → ℝ) (i : Fin M)
    (hb0 : ∀ k, 0 ≤ b k) (hbsum : ∑ k, b k ≤ 1) (hbi : 0 < b i) :
    (replaceMap b i) '' openSimplexFree ⊆ openSimplexFree := by sorry
