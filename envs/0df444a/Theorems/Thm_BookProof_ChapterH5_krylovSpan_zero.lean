-- Prove2me | Theorems.Thm_BookProof_ChapterH5_krylovSpan_zero
-- name    : BookProof.ChapterH5.krylovSpan_zero
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:53:09.969913+00:00
-- url     : https://prove2.me/theorems/641a9abe-ab95-498b-85c7-be10045494e6
-- title:
--   `BookProof.ChapterH5.krylovSpan_zero` : krylovSpan H v 0 = ⊥
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH5`.
--
--   `BookProof.ChapterH5.krylovSpan_zero` : krylovSpan H v 0 = ⊥
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH5.krylovSpan_zero`.

-- Generated from ChapterH5.lean — theorem BookProof.ChapterH5.krylovSpan_zero
import Mathlib
import Definitions.Def_ChapterH5
open BookProof.ChapterH5


noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterH5.krylovSpan_zero : krylovSpan H v 0 = ⊥ := by sorry
