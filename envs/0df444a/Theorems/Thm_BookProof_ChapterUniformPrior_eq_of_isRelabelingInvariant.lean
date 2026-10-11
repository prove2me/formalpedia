-- Prove2me | Theorems.Thm_BookProof_ChapterUniformPrior_eq_of_isRelabelingInvariant
-- name    : BookProof.ChapterUniformPrior.eq_of_isRelabelingInvariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:29:23.215078+00:00
-- url     : https://prove2.me/theorems/56f4ef8d-5685-4c83-b76d-668554df380c
-- title:
--   `BookProof.ChapterUniformPrior.eq_of_isRelabelingInvariant` (p : Hyp → ℝ) (hp : IsRelabelingInvariant p) (a b : Hyp) : p a = p b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUniformPrior`.
--
--   `BookProof.ChapterUniformPrior.eq_of_isRelabelingInvariant` (p : Hyp → ℝ) (hp : IsRelabelingInvariant p) (a b : Hyp) : p a = p b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUniformPrior.eq_of_isRelabelingInvariant`.

-- Generated from ChapterUniformPrior.lean — theorem BookProof.ChapterUniformPrior.eq_of_isRelabelingInvariant
import Mathlib
import Definitions.Def_ChapterUniformPrior
open BookProof.ChapterUniformPrior


open scoped BigOperators


variable {Hyp Data : Type*}

theorem BookProof.ChapterUniformPrior.eq_of_isRelabelingInvariant (p : Hyp → ℝ)
    (hp : IsRelabelingInvariant p) (a b : Hyp) : p a = p b := by sorry
