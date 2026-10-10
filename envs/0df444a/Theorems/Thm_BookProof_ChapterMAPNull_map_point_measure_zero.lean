-- Prove2me | Theorems.Thm_BookProof_ChapterMAPNull_map_point_measure_zero
-- name    : BookProof.ChapterMAPNull.map_point_measure_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:48:22.957928+00:00
-- url     : https://prove2.me/theorems/9c31d691-80f4-43f2-9cf3-3f1ca214a41b
-- title:
--   `BookProof.ChapterMAPNull.map_point_measure_zero` (μ : Measure α) [NullSingletonClass μ] (mapPoint : α) : μ {mapPoint} = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMAPNull`.
--
--   `BookProof.ChapterMAPNull.map_point_measure_zero` (μ : Measure α) [NullSingletonClass μ] (mapPoint : α) : μ {mapPoint} = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMAPNull.map_point_measure_zero`.

-- Generated from ChapterMAPNull.lean — theorem BookProof.ChapterMAPNull.map_point_measure_zero
import Mathlib
import Definitions.Def_ChapterMAPNull
open BookProof.ChapterMAPNull


open MeasureTheory


variable {α : Type*} [MeasurableSpace α]

theorem BookProof.ChapterMAPNull.map_point_measure_zero (μ : Measure α) [NullSingletonClass μ] (mapPoint : α) :
    μ {mapPoint} = 0 := by sorry
