-- Prove2me | Theorems.Thm_BookProof_ChapterMAPNull_maximizerSet_measure_zero
-- name    : BookProof.ChapterMAPNull.maximizerSet_measure_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:48:55.042233+00:00
-- url     : https://prove2.me/theorems/9413af4f-3649-4eca-87e4-76c116f06404
-- title:
--   `BookProof.ChapterMAPNull.maximizerSet_measure_zero` (μ : Measure α) [NullSingletonClass μ] (score : α → ℝ) (hcountable : (maximizerSet score).Countable) : μ (maximizerSet score) =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMAPNull`.
--
--   `BookProof.ChapterMAPNull.maximizerSet_measure_zero` (μ : Measure α) [NullSingletonClass μ] (score : α → ℝ) (hcountable : (maximizerSet score).Countable) : μ (maximizerSet score) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMAPNull.maximizerSet_measure_zero`.

-- Generated from ChapterMAPNull.lean — theorem BookProof.ChapterMAPNull.maximizerSet_measure_zero
import Mathlib
import Definitions.Def_ChapterMAPNull
open BookProof.ChapterMAPNull


open MeasureTheory


variable {α : Type*} [MeasurableSpace α]

theorem BookProof.ChapterMAPNull.maximizerSet_measure_zero (μ : Measure α) [NullSingletonClass μ]
    (score : α → ℝ) (hcountable : (maximizerSet score).Countable) :
    μ (maximizerSet score) = 0 := by sorry
