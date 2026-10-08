-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBorn_measurable_bornMap
-- name    : BookProof.ChapterFreeFieldBorn.measurable_bornMap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T05:01:05.253893+00:00
-- url     : https://prove2.me/theorems/7e91438e-fb34-47b2-90a4-6eb5e162399d
-- title:
--   `BookProof.ChapterFreeFieldBorn.measurable_bornMap` : Measurable (bornMap : EuclideanSpace ℝ (Fin n) → _)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBorn`.
--
--   `BookProof.ChapterFreeFieldBorn.measurable_bornMap` : Measurable (bornMap : EuclideanSpace ℝ (Fin n) → _)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBorn.measurable_bornMap`.

-- Generated from ChapterFreeFieldBorn.lean — theorem BookProof.ChapterFreeFieldBorn.measurable_bornMap
import Definitions.Def_ChapterFreeFieldGaussian
import Definitions.Def_ChapterFreeFieldSphere
import Definitions.Def_ChapterFreeFieldSphereSupport
import Mathlib
import Definitions.Def_ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBorn

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphereSupport

theorem BookProof.ChapterFreeFieldBorn.measurable_bornMap : Measurable (bornMap : EuclideanSpace ℝ (Fin n) → _) := by sorry
