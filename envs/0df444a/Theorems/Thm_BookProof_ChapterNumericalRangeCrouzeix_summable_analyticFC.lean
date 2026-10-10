-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_summable_analyticFC
-- name    : BookProof.ChapterNumericalRangeCrouzeix.summable_analyticFC
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:15:53.99003+00:00
-- url     : https://prove2.me/theorems/bd932f11-bc79-4486-afdb-9866e5771c01
-- title:
--   `BookProof.ChapterNumericalRangeCrouzeix.summable_analyticFC` [CompleteSpace E] {A : E →L[ℂ] E} {r M R : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M) (hR : r < R) (h : NumRadiusLE A r) {a : ℕ → ℂ}
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeCrouzeix`.
--
--   `BookProof.ChapterNumericalRangeCrouzeix.summable_analyticFC` [CompleteSpace E] {A : E →L[ℂ] E} {r M R : ℝ} (hr : 0 ≤ r) (hM : 0 ≤ M) (hR : r < R) (h : NumRadiusLE A r) {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ M / R ^ n) : Summable fun n : ℕ => a n • A ^ n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeCrouzeix.summable_analyticFC`.

-- Generated from ChapterNumericalRangeCrouzeix.lean — theorem BookProof.ChapterNumericalRangeCrouzeix.summable_analyticFC
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterNumericalRangeCrouzeix.summable_analyticFC [CompleteSpace E] {A : E →L[ℂ] E} {r M R : ℝ} (hr : 0 ≤ r)
    (hM : 0 ≤ M) (hR : r < R) (h : NumRadiusLE A r) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ M / R ^ n) : Summable fun n : ℕ => a n • A ^ n := by sorry
