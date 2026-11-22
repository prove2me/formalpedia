-- Prove2me | Theorems.Thm_BornVolume_image_openSimplexFree_measurableSet
-- name    : BornVolume.image_openSimplexFree_measurableSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:05:46.185272+00:00
-- url     : https://prove2.me/theorems/ad755a78-6dde-4fc0-865a-1b86e822df3a
-- title:
--   Born Volume: image open Simplex Free measurable Set
-- statement:
--   **Det-free measurability of continuous images of the open simplex.** The
--   continuous image of a σ-compact set is σ-compact — a countable union of
--   compacts, each closed (T2) hence Borel. This works when `det = 0`, where the image is
--   not open.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L61-L65
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean#L61-L65

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

theorem BornVolume.image_openSimplexFree_measurableSet {f : (Fin M → ℝ) → (Fin M → ℝ)}
    (hf : Continuous f) : MeasurableSet (f '' openSimplexFree) := by sorry
