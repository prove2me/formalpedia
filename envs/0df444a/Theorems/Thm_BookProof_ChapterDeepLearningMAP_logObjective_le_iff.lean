-- Prove2me | Theorems.Thm_BookProof_ChapterDeepLearningMAP_logObjective_le_iff
-- name    : BookProof.ChapterDeepLearningMAP.logObjective_le_iff
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:27:58.054705+00:00
-- url     : https://prove2.me/theorems/3275bee8-2387-42aa-8455-900ab69a7566
-- title:
--   `BookProof.ChapterDeepLearningMAP.logObjective_le_iff` (prior : Model → ℝ) (likelihood : Model → Data → ℝ) (d : Data) (hprior : ∀ m, 0 < prior m) (hlike : ∀ m, 0 < likelihood m d)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDeepLearningMAP`.
--
--   `BookProof.ChapterDeepLearningMAP.logObjective_le_iff` (prior : Model → ℝ) (likelihood : Model → Data → ℝ) (d : Data) (hprior : ∀ m, 0 < prior m) (hlike : ∀ m, 0 < likelihood m d) (a b : Model) : logObjective prior likelihood d a ≤ logObjective prior likelihood d b ↔ posteriorWeight prior likelihood d a ≤ posteriorWeight prior likelihood d b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDeepLearningMAP.logObjective_le_iff`.

-- Generated from ChapterDeepLearningMAP.lean — theorem BookProof.ChapterDeepLearningMAP.logObjective_le_iff
import Mathlib
import Definitions.Def_ChapterDeepLearningMAP
open BookProof.ChapterDeepLearningMAP



variable {Model Data : Type*}

theorem BookProof.ChapterDeepLearningMAP.logObjective_le_iff (prior : Model → ℝ)
    (likelihood : Model → Data → ℝ) (d : Data)
    (hprior : ∀ m, 0 < prior m) (hlike : ∀ m, 0 < likelihood m d)
    (a b : Model) :
    logObjective prior likelihood d a ≤ logObjective prior likelihood d b ↔
      posteriorWeight prior likelihood d a ≤ posteriorWeight prior likelihood d b := by sorry
