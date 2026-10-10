-- Prove2me | Theorems.Thm_BookProof_ChapterMAPNull_countable_map_set_measure_zero
-- name    : BookProof.ChapterMAPNull.countable_map_set_measure_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:48:39.28932+00:00
-- url     : https://prove2.me/theorems/74a4cbeb-c73c-441e-833a-4f4af66e8992
-- title:
--   `BookProof.ChapterMAPNull.countable_map_set_measure_zero` (μ : Measure α) [NullSingletonClass μ] (maximizers : Set α) (hcountable : maximizers.Countable) : μ maximizers = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMAPNull`.
--
--   `BookProof.ChapterMAPNull.countable_map_set_measure_zero` (μ : Measure α) [NullSingletonClass μ] (maximizers : Set α) (hcountable : maximizers.Countable) : μ maximizers = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMAPNull.countable_map_set_measure_zero`.

-- Generated from ChapterMAPNull.lean — theorem BookProof.ChapterMAPNull.countable_map_set_measure_zero
import Mathlib
import Definitions.Def_ChapterMAPNull
open BookProof.ChapterMAPNull


open MeasureTheory


variable {α : Type*} [MeasurableSpace α]

theorem BookProof.ChapterMAPNull.countable_map_set_measure_zero (μ : Measure α) [NullSingletonClass μ]
    (maximizers : Set α) (hcountable : maximizers.Countable) :
    μ maximizers = 0 := by sorry
