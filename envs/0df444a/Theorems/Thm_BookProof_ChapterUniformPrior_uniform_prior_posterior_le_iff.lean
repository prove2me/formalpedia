-- Prove2me | Theorems.Thm_BookProof_ChapterUniformPrior_uniform_prior_posterior_le_iff
-- name    : BookProof.ChapterUniformPrior.uniform_prior_posterior_le_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:18:37.941249+00:00
-- url     : https://prove2.me/theorems/0c42662e-8565-42c9-bc09-61abcdba3706
-- title:
--   `BookProof.ChapterUniformPrior.uniform_prior_posterior_le_iff` [Fintype Hyp] (likelihood : Hyp → Data → ℝ) (d : Data) (c : ℝ) (hc : 0 < c) (hevidence : 0 < BookProof.ChapterBayesIn
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUniformPrior`.
--
--   `BookProof.ChapterUniformPrior.uniform_prior_posterior_le_iff` [Fintype Hyp] (likelihood : Hyp → Data → ℝ) (d : Data) (c : ℝ) (hc : 0 < c) (hevidence : 0 < BookProof.ChapterBayesInference.evidence (fun _ : Hyp => c) likelihood d) (a b : Hyp) : BookProof.ChapterBayesInference.posterior (fun _ : Hyp => c) likelihood d a ≤ BookProof.ChapterBayesInference.posterior (fun _ : Hyp => c) likelihood d b ↔ likelihood a d ≤ likelihood b d
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUniformPrior.uniform_prior_posterior_le_iff`.

-- Generated from ChapterUniformPrior.lean — theorem BookProof.ChapterUniformPrior.uniform_prior_posterior_le_iff
import Mathlib
import Definitions.Def_ChapterUniformPrior
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference
open BookProof.ChapterUniformPrior


open scoped BigOperators


variable {Hyp Data : Type*}

theorem BookProof.ChapterUniformPrior.uniform_prior_posterior_le_iff [Fintype Hyp]
    (likelihood : Hyp → Data → ℝ) (d : Data) (c : ℝ)
    (hc : 0 < c)
    (hevidence : 0 < BookProof.ChapterBayesInference.evidence (fun _ : Hyp => c) likelihood d)
    (a b : Hyp) :
    BookProof.ChapterBayesInference.posterior (fun _ : Hyp => c) likelihood d a ≤
        BookProof.ChapterBayesInference.posterior (fun _ : Hyp => c) likelihood d b ↔
      likelihood a d ≤ likelihood b d := by sorry
