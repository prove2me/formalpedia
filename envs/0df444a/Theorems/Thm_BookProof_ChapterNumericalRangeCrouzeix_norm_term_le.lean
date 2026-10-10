-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_norm_term_le
-- name    : BookProof.ChapterNumericalRangeCrouzeix.norm_term_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:15:18.048493+00:00
-- url     : https://prove2.me/theorems/f3d42678-6b03-4ac8-86a8-9e401f827a3d
-- title:
--   `BookProof.ChapterNumericalRangeCrouzeix.norm_term_le` [CompleteSpace E] {A : E →L[ℂ] E} {r M R : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M) (hR : r < R) (h : NumRadiusLE A r) {a : ℕ → ℂ} (ha :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeCrouzeix`.
--
--   `BookProof.ChapterNumericalRangeCrouzeix.norm_term_le` [CompleteSpace E] {A : E →L[ℂ] E} {r M R : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M) (hR : r < R) (h : NumRadiusLE A r) {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ M / R ^ n) (n : ℕ) (hn : 0 < n) : ‖a n • A ^ n‖ ≤ 2 * M * (r / R) ^ n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeCrouzeix.norm_term_le`.

-- Generated from ChapterNumericalRangeCrouzeix.lean — theorem BookProof.ChapterNumericalRangeCrouzeix.norm_term_le
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterNumericalRangeCrouzeix.norm_term_le [CompleteSpace E] {A : E →L[ℂ] E} {r M R : ℝ} (hr : 0 ≤ r)
    (hM : 0 ≤ M) (hR : r < R) (h : NumRadiusLE A r) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ M / R ^ n) (n : ℕ) (hn : 0 < n) :
    ‖a n • A ^ n‖ ≤ 2 * M * (r / R) ^ n := by sorry
