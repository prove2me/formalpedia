-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_inner_polar_bound
-- name    : BookProof.ChapterNumericalRangeCrouzeix.inner_polar_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:15:32.211273+00:00
-- url     : https://prove2.me/theorems/0a05cc1f-ddc3-4e55-b5e5-f0c7269a0fe5
-- title:
--   `BookProof.ChapterNumericalRangeCrouzeix.inner_polar_bound` {A : E →L[ℂ] E} {r : ℝ} (h : NumRadiusLE A r) (x y : E) : ‖(⟪A y, x⟫_ℂ)‖ ≤ r * (‖x‖ ^ 2 + ‖y‖ ^ 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeCrouzeix`.
--
--   `BookProof.ChapterNumericalRangeCrouzeix.inner_polar_bound` {A : E →L[ℂ] E} {r : ℝ} (h : NumRadiusLE A r) (x y : E) : ‖(⟪A y, x⟫_ℂ)‖ ≤ r * (‖x‖ ^ 2 + ‖y‖ ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeCrouzeix.inner_polar_bound`.

-- Generated from ChapterNumericalRangeCrouzeix.lean — theorem BookProof.ChapterNumericalRangeCrouzeix.inner_polar_bound
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterNumericalRangeCrouzeix.inner_polar_bound {A : E →L[ℂ] E} {r : ℝ} (h : NumRadiusLE A r) (x y : E) :
    ‖(⟪A y, x⟫_ℂ)‖ ≤ r * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by sorry
