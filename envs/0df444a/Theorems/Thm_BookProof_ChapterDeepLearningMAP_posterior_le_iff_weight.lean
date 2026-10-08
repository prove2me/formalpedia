-- Prove2me | Theorems.Thm_BookProof_ChapterDeepLearningMAP_posterior_le_iff_weight
-- name    : BookProof.ChapterDeepLearningMAP.posterior_le_iff_weight
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:28:08.687549+00:00
-- url     : https://prove2.me/theorems/ce10c899-7a79-4f23-a9ed-11542ca82070
-- title:
--   `BookProof.ChapterDeepLearningMAP.posterior_le_iff_weight` (prior : Model → ℝ) (likelihood : Model → Data → ℝ) (d : Data) (hevidence : 0 < BookProof.ChapterBayesInference.evidence
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDeepLearningMAP`.
--
--   `BookProof.ChapterDeepLearningMAP.posterior_le_iff_weight` (prior : Model → ℝ) (likelihood : Model → Data → ℝ) (d : Data) (hevidence : 0 < BookProof.ChapterBayesInference.evidence prior likelihood d) (a b : Model) : BookProof.ChapterBayesInference.posterior prior likelihood d a ≤ BookProof.ChapterBayesInference.posterior prior likelihood d b ↔ posteriorWeight prior likelihood d a ≤ posteriorWeight prior likelihood d b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterDeepLearningMAP.posterior_le_iff_weight`.

-- Generated from ChapterDeepLearningMAP.lean — theorem BookProof.ChapterDeepLearningMAP.posterior_le_iff_weight
import Mathlib
import Definitions.Def_ChapterDeepLearningMAP
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference
open BookProof.ChapterDeepLearningMAP



variable {Model Data : Type*}

variable [Fintype Model]

theorem BookProof.ChapterDeepLearningMAP.posterior_le_iff_weight (prior : Model → ℝ)
    (likelihood : Model → Data → ℝ) (d : Data)
    (hevidence : 0 < BookProof.ChapterBayesInference.evidence prior likelihood d)
    (a b : Model) :
    BookProof.ChapterBayesInference.posterior prior likelihood d a ≤
      BookProof.ChapterBayesInference.posterior prior likelihood d b ↔
    posteriorWeight prior likelihood d a ≤ posteriorWeight prior likelihood d b := by sorry
