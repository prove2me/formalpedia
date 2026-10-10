-- Prove2me | Theorems.Thm_BookProof_ChapterPriorDependence_distinct_priors_distinct_posteriors
-- name    : BookProof.ChapterPriorDependence.distinct_priors_distinct_posteriors
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:55:33.014846+00:00
-- url     : https://prove2.me/theorems/ce3aea9b-40b3-4862-98f7-08f4162e5f74
-- title:
--   `BookProof.ChapterPriorDependence.distinct_priors_distinct_posteriors` (a b : Hyp) (hab : a ≠ b) (L : Hyp → Data → ℝ) (d : Data) (ha : 0 < L a d) : BookProof.ChapterBayesInference.
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPriorDependence`.
--
--   `BookProof.ChapterPriorDependence.distinct_priors_distinct_posteriors` (a b : Hyp) (hab : a ≠ b) (L : Hyp → Data → ℝ) (d : Data) (ha : 0 < L a d) : BookProof.ChapterBayesInference.posterior (diracPrior a) L d ≠ BookProof.ChapterBayesInference.posterior (diracPrior b) L d
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterPriorDependence.distinct_priors_distinct_posteriors`.

-- Generated from ChapterPriorDependence.lean — theorem BookProof.ChapterPriorDependence.distinct_priors_distinct_posteriors
import Mathlib
import Definitions.Def_ChapterPriorDependence
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference
open BookProof.ChapterPriorDependence


open scoped BigOperators


variable {Hyp Data : Type*} [DecidableEq Hyp]

variable [Fintype Hyp]

theorem BookProof.ChapterPriorDependence.distinct_priors_distinct_posteriors (a b : Hyp) (hab : a ≠ b)
    (L : Hyp → Data → ℝ) (d : Data) (ha : 0 < L a d) :
    BookProof.ChapterBayesInference.posterior (diracPrior a) L d ≠
      BookProof.ChapterBayesInference.posterior (diracPrior b) L d := by sorry
