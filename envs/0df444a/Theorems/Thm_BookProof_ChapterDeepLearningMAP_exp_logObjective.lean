-- Prove2me | Theorems.Thm_BookProof_ChapterDeepLearningMAP_exp_logObjective
-- name    : BookProof.ChapterDeepLearningMAP.exp_logObjective
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:28:33.678367+00:00
-- url     : https://prove2.me/theorems/146c5864-9392-4c70-a2db-2ad0d419e94d
-- title:
--   `BookProof.ChapterDeepLearningMAP.exp_logObjective` (prior : Model → ℝ) (likelihood : Model → Data → ℝ) (d : Data) (hprior : ∀ m, 0 < prior m) (hlike : ∀ m, 0 < likelihood m d) (m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDeepLearningMAP`.
--
--   `BookProof.ChapterDeepLearningMAP.exp_logObjective` (prior : Model → ℝ) (likelihood : Model → Data → ℝ) (d : Data) (hprior : ∀ m, 0 < prior m) (hlike : ∀ m, 0 < likelihood m d) (m : Model) : Real.exp (logObjective prior likelihood d m) = posteriorWeight prior likelihood d m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDeepLearningMAP.exp_logObjective`.

-- Generated from ChapterDeepLearningMAP.lean — theorem BookProof.ChapterDeepLearningMAP.exp_logObjective
import Mathlib
import Definitions.Def_ChapterDeepLearningMAP
open BookProof.ChapterDeepLearningMAP



variable {Model Data : Type*}

theorem BookProof.ChapterDeepLearningMAP.exp_logObjective (prior : Model → ℝ) (likelihood : Model → Data → ℝ)
    (d : Data) (hprior : ∀ m, 0 < prior m)
    (hlike : ∀ m, 0 < likelihood m d) (m : Model) :
    Real.exp (logObjective prior likelihood d m) =
      posteriorWeight prior likelihood d m := by sorry
