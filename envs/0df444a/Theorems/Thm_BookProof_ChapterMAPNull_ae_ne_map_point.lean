-- Prove2me | Theorems.Thm_BookProof_ChapterMAPNull_ae_ne_map_point
-- name    : BookProof.ChapterMAPNull.ae_ne_map_point
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:48:31.692374+00:00
-- url     : https://prove2.me/theorems/b6c9e789-cc6e-407a-9dea-961fff8294ea
-- title:
--   `BookProof.ChapterMAPNull.ae_ne_map_point` (μ : Measure α) [NullSingletonClass μ] (mapPoint : α) : ∀ᵐ x ∂μ, x ≠ mapPoint
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMAPNull`.
--
--   `BookProof.ChapterMAPNull.ae_ne_map_point` (μ : Measure α) [NullSingletonClass μ] (mapPoint : α) : ∀ᵐ x ∂μ, x ≠ mapPoint
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMAPNull.ae_ne_map_point`.

-- Generated from ChapterMAPNull.lean — theorem BookProof.ChapterMAPNull.ae_ne_map_point
import Mathlib
import Definitions.Def_ChapterMAPNull
open BookProof.ChapterMAPNull


open MeasureTheory


variable {α : Type*} [MeasurableSpace α]

theorem BookProof.ChapterMAPNull.ae_ne_map_point (μ : Measure α) [NullSingletonClass μ] (mapPoint : α) :
    ∀ᵐ x ∂μ, x ≠ mapPoint := by sorry
