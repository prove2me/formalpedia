-- Prove2me | Theorems.Thm_BookProof_ChapterUniformPrior_isRelabelingInvariant_iff_constant
-- name    : BookProof.ChapterUniformPrior.isRelabelingInvariant_iff_constant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:29:34.094987+00:00
-- url     : https://prove2.me/theorems/0bdbad78-497b-4e22-8af0-75d42d625d29
-- title:
--   `BookProof.ChapterUniformPrior.isRelabelingInvariant_iff_constant` (p : Hyp → ℝ) : IsRelabelingInvariant p ↔ ∃ c : ℝ, p = fun _ => c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUniformPrior`.
--
--   `BookProof.ChapterUniformPrior.isRelabelingInvariant_iff_constant` (p : Hyp → ℝ) : IsRelabelingInvariant p ↔ ∃ c : ℝ, p = fun _ => c
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUniformPrior.isRelabelingInvariant_iff_constant`.

-- Generated from ChapterUniformPrior.lean — theorem BookProof.ChapterUniformPrior.isRelabelingInvariant_iff_constant
import Mathlib
import Definitions.Def_ChapterUniformPrior
open BookProof.ChapterUniformPrior


open scoped BigOperators


variable {Hyp Data : Type*}

theorem BookProof.ChapterUniformPrior.isRelabelingInvariant_iff_constant (p : Hyp → ℝ) :
    IsRelabelingInvariant p ↔ ∃ c : ℝ, p = fun _ => c := by sorry
