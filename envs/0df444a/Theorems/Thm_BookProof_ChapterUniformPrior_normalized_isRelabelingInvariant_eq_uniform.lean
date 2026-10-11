-- Prove2me | Theorems.Thm_BookProof_ChapterUniformPrior_normalized_isRelabelingInvariant_eq_uniform
-- name    : BookProof.ChapterUniformPrior.normalized_isRelabelingInvariant_eq_uniform
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:29:37.563415+00:00
-- url     : https://prove2.me/theorems/6e71a356-603d-4608-913c-fd14c4ab2c3f
-- title:
--   `BookProof.ChapterUniformPrior.normalized_isRelabelingInvariant_eq_uniform` [Fintype Hyp] [Nonempty Hyp] (p : Hyp → ℝ) (hp : IsRelabelingInvariant p) (hsum : ∑ x, p x = 1) : p = fu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUniformPrior`.
--
--   `BookProof.ChapterUniformPrior.normalized_isRelabelingInvariant_eq_uniform` [Fintype Hyp] [Nonempty Hyp] (p : Hyp → ℝ) (hp : IsRelabelingInvariant p) (hsum : ∑ x, p x = 1) : p = fun _ => (1 : ℝ) / Fintype.card Hyp
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUniformPrior.normalized_isRelabelingInvariant_eq_uniform`.

-- Generated from ChapterUniformPrior.lean — theorem BookProof.ChapterUniformPrior.normalized_isRelabelingInvariant_eq_uniform
import Mathlib
import Definitions.Def_ChapterUniformPrior
open BookProof.ChapterUniformPrior


open scoped BigOperators


variable {Hyp Data : Type*}

theorem BookProof.ChapterUniformPrior.normalized_isRelabelingInvariant_eq_uniform [Fintype Hyp] [Nonempty Hyp]
    (p : Hyp → ℝ) (hp : IsRelabelingInvariant p) (hsum : ∑ x, p x = 1) :
    p = fun _ => (1 : ℝ) / Fintype.card Hyp := by sorry
