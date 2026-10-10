-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_numRadiusLE_pow
-- name    : BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_pow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:14:29.205546+00:00
-- url     : https://prove2.me/theorems/de49ee9d-de67-410c-a712-35047968dab2
-- title:
--   `BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_pow` {A : E →L[ℂ] E} {r : ℝ} (hr : 0 ≤ r) (h : NumRadiusLE A r) (n : ℕ) (hn : 0 < n) : NumRadiusLE (A ^ n) (r ^ n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeCrouzeix`.
--
--   `BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_pow` {A : E →L[ℂ] E} {r : ℝ} (hr : 0 ≤ r) (h : NumRadiusLE A r) (n : ℕ) (hn : 0 < n) : NumRadiusLE (A ^ n) (r ^ n)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_pow`.

-- Generated from ChapterNumericalRangeCrouzeix.lean — theorem BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_pow
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_pow {A : E →L[ℂ] E} {r : ℝ} (hr : 0 ≤ r) (h : NumRadiusLE A r) (n : ℕ)
    (hn : 0 < n) : NumRadiusLE (A ^ n) (r ^ n) := by sorry
