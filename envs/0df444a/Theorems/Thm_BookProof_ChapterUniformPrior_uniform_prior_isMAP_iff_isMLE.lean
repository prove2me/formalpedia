-- Prove2me | Theorems.Thm_BookProof_ChapterUniformPrior_uniform_prior_isMAP_iff_isMLE
-- name    : BookProof.ChapterUniformPrior.uniform_prior_isMAP_iff_isMLE
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:30:11.922787+00:00
-- url     : https://prove2.me/theorems/01b82a86-b0c6-44ff-9c2c-0f5bf30a0406
-- title:
--   `BookProof.ChapterUniformPrior.uniform_prior_isMAP_iff_isMLE` [Fintype Hyp] (likelihood : Hyp → Data → ℝ) (d : Data) (c : ℝ) (hc : 0 < c) (hevidence : 0 < BookProof.ChapterBayesInf
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUniformPrior`.
--
--   `BookProof.ChapterUniformPrior.uniform_prior_isMAP_iff_isMLE` [Fintype Hyp] (likelihood : Hyp → Data → ℝ) (d : Data) (c : ℝ) (hc : 0 < c) (hevidence : 0 < BookProof.ChapterBayesInference.evidence (fun _ : Hyp => c) likelihood d) (best : Hyp) : (∀ m, BookProof.ChapterBayesInference.posterior (fun _ : Hyp => c) likelihood d m ≤ BookProof.ChapterBayesInference.posterior (fun _ : Hyp => c) likelihood d best) ↔ ∀ m, likelihood m d ≤ likelihood best d
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUniformPrior.uniform_prior_isMAP_iff_isMLE`.

-- Generated from ChapterUniformPrior.lean — theorem BookProof.ChapterUniformPrior.uniform_prior_isMAP_iff_isMLE
import Mathlib
import Definitions.Def_ChapterUniformPrior
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference
open BookProof.ChapterUniformPrior


open scoped BigOperators


variable {Hyp Data : Type*}

theorem BookProof.ChapterUniformPrior.uniform_prior_isMAP_iff_isMLE [Fintype Hyp]
    (likelihood : Hyp → Data → ℝ) (d : Data) (c : ℝ)
    (hc : 0 < c)
    (hevidence : 0 < BookProof.ChapterBayesInference.evidence (fun _ : Hyp => c) likelihood d)
    (best : Hyp) :
    (∀ m, BookProof.ChapterBayesInference.posterior (fun _ : Hyp => c) likelihood d m ≤
        BookProof.ChapterBayesInference.posterior (fun _ : Hyp => c) likelihood d best) ↔
      ∀ m, likelihood m d ≤ likelihood best d := by sorry
