-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_crouzeix_ball
-- name    : BookProof.ChapterNumericalRangeCrouzeix.crouzeix_ball
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:16:04.321428+00:00
-- url     : https://prove2.me/theorems/3b4d97ac-382a-47a6-9c9c-39cd15e65240
-- title:
--   `BookProof.ChapterNumericalRangeCrouzeix.crouzeix_ball` [CompleteSpace E] {A : E →L[ℂ] E} {c : ℂ} {r M R : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M) (hR : r < R) (h : NumBallLE A c r) {a : ℕ →
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeCrouzeix`.
--
--   `BookProof.ChapterNumericalRangeCrouzeix.crouzeix_ball` [CompleteSpace E] {A : E →L[ℂ] E} {c : ℂ} {r M R : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M) (hR : r < R) (h : NumBallLE A c r) {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ M / R ^ n) : ‖analyticFC a (A - c • (1 : E →L[ℂ] E))‖ ≤ (1 + 2 * r / (R - r)) * M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeCrouzeix.crouzeix_ball`.

-- Generated from ChapterNumericalRangeCrouzeix.lean — theorem BookProof.ChapterNumericalRangeCrouzeix.crouzeix_ball
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterNumericalRangeCrouzeix.crouzeix_ball [CompleteSpace E] {A : E →L[ℂ] E} {c : ℂ} {r M R : ℝ} (hr : 0 ≤ r)
    (hM : 0 ≤ M) (hR : r < R) (h : NumBallLE A c r) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ M / R ^ n) :
    ‖analyticFC a (A - c • (1 : E →L[ℂ] E))‖ ≤ (1 + 2 * r / (R - r)) * M := by sorry
