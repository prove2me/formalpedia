-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_crouzeix_disc
-- name    : BookProof.ChapterNumericalRangeCrouzeix.crouzeix_disc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:15:24.378357+00:00
-- url     : https://prove2.me/theorems/e4fe7e61-ce5a-4df8-b15b-45fc44e003fc
-- title:
--   `BookProof.ChapterNumericalRangeCrouzeix.crouzeix_disc` [CompleteSpace E] {A : E →L[ℂ] E} {r M R : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M) (hR : r < R) (h : NumRadiusLE A r) {a : ℕ → ℂ} (ha :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeCrouzeix`.
--
--   `BookProof.ChapterNumericalRangeCrouzeix.crouzeix_disc` [CompleteSpace E] {A : E →L[ℂ] E} {r M R : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M) (hR : r < R) (h : NumRadiusLE A r) {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ M / R ^ n) : ‖analyticFC a A‖ ≤ (1 + 2 * r / (R - r)) * M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeCrouzeix.crouzeix_disc`.

-- Generated from ChapterNumericalRangeCrouzeix.lean — theorem BookProof.ChapterNumericalRangeCrouzeix.crouzeix_disc
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterNumericalRangeCrouzeix.crouzeix_disc [CompleteSpace E] {A : E →L[ℂ] E} {r M R : ℝ} (hr : 0 ≤ r)
    (hM : 0 ≤ M) (hR : r < R) (h : NumRadiusLE A r) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ M / R ^ n) :
    ‖analyticFC a A‖ ≤ (1 + 2 * r / (R - r)) * M := by sorry
