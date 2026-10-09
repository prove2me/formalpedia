-- Prove2me | Theorems.Thm_BookProof_ChapterH5_krylovSpan_map_le
-- name    : BookProof.ChapterH5.krylovSpan_map_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:53:07.842641+00:00
-- url     : https://prove2.me/theorems/0ce88097-ee37-45ff-bcf0-b81f9afabc0c
-- title:
--   `BookProof.ChapterH5.krylovSpan_map_le` (m : ℕ) : Submodule.map H (krylovSpan H v m) ≤ krylovSpan H v (m + 1)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH5`.
--
--   `BookProof.ChapterH5.krylovSpan_map_le` (m : ℕ) : Submodule.map H (krylovSpan H v m) ≤ krylovSpan H v (m + 1)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH5.krylovSpan_map_le`.

-- Generated from ChapterH5.lean — theorem BookProof.ChapterH5.krylovSpan_map_le
import Mathlib
import Definitions.Def_ChapterH5
open BookProof.ChapterH5


noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {H : E →ₗ[K] E} {v : E}

theorem BookProof.ChapterH5.krylovSpan_map_le (m : ℕ) :
    Submodule.map H (krylovSpan H v m) ≤ krylovSpan H v (m + 1) := by sorry
