-- Prove2me | Theorems.Thm_BornVolume_apexMap_image_subset_of_closedSimplex
-- name    : BornVolume.apexMap_image_subset_of_closedSimplex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:06:28.238848+00:00
-- url     : https://prove2.me/theorems/59d2a9fa-d9fc-4639-8ff8-9b639d9bc7db
-- title:
--   Born Volume: apex Map image subset of closed Simplex
-- statement:
--   **The cell opposite the origin `0` (the last outcome) lies in the open simplex**, assuming
--   only `0 ≤ b` and `∑ b < 1` (its weight is `1 − ∑ b`).
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L124-L138
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L124-L138

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

theorem BornVolume.apexMap_image_subset_of_closedSimplex (b : Fin M → ℝ)
    (hb0 : ∀ k, 0 ≤ b k) (hbsum : ∑ k, b k < 1) :
    (fun x => apexLin b x + b) '' openSimplexFree ⊆ openSimplexFree := by sorry
