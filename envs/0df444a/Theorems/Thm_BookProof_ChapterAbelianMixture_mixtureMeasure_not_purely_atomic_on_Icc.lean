-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianMixture_mixtureMeasure_not_purely_atomic_on_Icc
-- name    : BookProof.ChapterAbelianMixture.mixtureMeasure_not_purely_atomic_on_Icc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:51:23.18713+00:00
-- url     : https://prove2.me/theorems/32b0e651-cd2b-45a9-9c3f-1d6fd50803e5
-- title:
--   `BookProof.ChapterAbelianMixture.mixtureMeasure_not_purely_atomic_on_Icc` : 0 < mixtureMeasure (Set.Icc (0 : ℝ) 1) ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, mixtureMeasure {x} = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianMixture`.
--
--   `BookProof.ChapterAbelianMixture.mixtureMeasure_not_purely_atomic_on_Icc` : 0 < mixtureMeasure (Set.Icc (0 : ℝ) 1) ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, mixtureMeasure {x} = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianMixture.mixtureMeasure_not_purely_atomic_on_Icc`.

-- Generated from ChapterAbelianMixture.lean — theorem BookProof.ChapterAbelianMixture.mixtureMeasure_not_purely_atomic_on_Icc
import Mathlib
import Definitions.Def_ChapterAbelianMixture
open BookProof.ChapterAbelianMixture


noncomputable section

open MeasureTheory ENNReal

theorem BookProof.ChapterAbelianMixture.mixtureMeasure_not_purely_atomic_on_Icc :
    0 < mixtureMeasure (Set.Icc (0 : ℝ) 1) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, mixtureMeasure {x} = 0 := by sorry
