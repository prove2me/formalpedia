-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_inner_self_re
-- name    : BookProof.ChapterNumericalRangeCrouzeix.inner_self_re
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:13:48.381979+00:00
-- url     : https://prove2.me/theorems/acd22cd9-63a3-4ce7-98b3-b5ff8233a087
-- title:
--   `BookProof.ChapterNumericalRangeCrouzeix.inner_self_re` (x : E) : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeCrouzeix`.
--
--   `BookProof.ChapterNumericalRangeCrouzeix.inner_self_re` (x : E) : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeCrouzeix.inner_self_re`.

-- Generated from ChapterNumericalRangeCrouzeix.lean — theorem BookProof.ChapterNumericalRangeCrouzeix.inner_self_re
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterNumericalRangeCrouzeix.inner_self_re (x : E) : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by sorry
