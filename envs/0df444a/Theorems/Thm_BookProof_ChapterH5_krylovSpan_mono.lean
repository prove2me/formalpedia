-- Prove2me | Theorems.Thm_BookProof_ChapterH5_krylovSpan_mono
-- name    : BookProof.ChapterH5.krylovSpan_mono
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T20:14:52.010751+00:00
-- url     : https://prove2.me/theorems/a4d5d598-8d7b-4c7b-8383-3a687f8675d9
-- title:
--   `BookProof.ChapterH5.krylovSpan_mono` {m n : ℕ} (hmn : m ≤ n) : krylovSpan H v m ≤ krylovSpan H v n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH5`.
--
--   `BookProof.ChapterH5.krylovSpan_mono` {m n : ℕ} (hmn : m ≤ n) : krylovSpan H v m ≤ krylovSpan H v n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH5.krylovSpan_mono`.

-- Generated from ChapterH5.lean — theorem BookProof.ChapterH5.krylovSpan_mono
import Mathlib
import Definitions.Def_ChapterH5
open BookProof.ChapterH5


noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterH5.krylovSpan_mono {m n : ℕ} (hmn : m ≤ n) :
    krylovSpan H v m ≤ krylovSpan H v n := by sorry
