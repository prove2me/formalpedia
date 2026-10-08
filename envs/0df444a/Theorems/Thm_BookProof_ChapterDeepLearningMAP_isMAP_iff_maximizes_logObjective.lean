-- Prove2me | Theorems.Thm_BookProof_ChapterDeepLearningMAP_isMAP_iff_maximizes_logObjective
-- name    : BookProof.ChapterDeepLearningMAP.isMAP_iff_maximizes_logObjective
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:28:39.324024+00:00
-- url     : https://prove2.me/theorems/78173cbc-7206-451d-935d-1a7d88f640b2
-- title:
--   `BookProof.ChapterDeepLearningMAP.isMAP_iff_maximizes_logObjective` (prior : Model → ℝ) (likelihood : Model → Data → ℝ) (d : Data) (hprior : ∀ m, 0 < prior m) (hlike : ∀ m, 0 < lik
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDeepLearningMAP`.
--
--   `BookProof.ChapterDeepLearningMAP.isMAP_iff_maximizes_logObjective` (prior : Model → ℝ) (likelihood : Model → Data → ℝ) (d : Data) (hprior : ∀ m, 0 < prior m) (hlike : ∀ m, 0 < likelihood m d) (hevidence : 0 < BookProof.ChapterBayesInference.evidence prior likelihood d) (best : Model) : (∀ m, BookProof.ChapterBayesInference.posterior prior likelihood d m ≤ BookProof.ChapterBayesInference.posterior prior likelihood d best) ↔ (∀ m, logObjective prior likelihood d m ≤ logObjective prior likelihood d best)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDeepLearningMAP.isMAP_iff_maximizes_logObjective`.

-- Generated from ChapterDeepLearningMAP.lean — theorem BookProof.ChapterDeepLearningMAP.isMAP_iff_maximizes_logObjective
import Mathlib
import Definitions.Def_ChapterDeepLearningMAP
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference
open BookProof.ChapterDeepLearningMAP



variable {Model Data : Type*}

variable [Fintype Model]

theorem BookProof.ChapterDeepLearningMAP.isMAP_iff_maximizes_logObjective (prior : Model → ℝ)
    (likelihood : Model → Data → ℝ) (d : Data)
    (hprior : ∀ m, 0 < prior m) (hlike : ∀ m, 0 < likelihood m d)
    (hevidence : 0 < BookProof.ChapterBayesInference.evidence prior likelihood d)
    (best : Model) :
    (∀ m, BookProof.ChapterBayesInference.posterior prior likelihood d m ≤
      BookProof.ChapterBayesInference.posterior prior likelihood d best) ↔
    (∀ m, logObjective prior likelihood d m ≤
      logObjective prior likelihood d best) := by sorry
