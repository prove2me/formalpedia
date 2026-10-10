-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeSemigroup_norm_cexp_le_of_re_le
-- name    : BookProof.ChapterNumericalRangeSemigroup.norm_cexp_le_of_re_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:37:36.342534+00:00
-- url     : https://prove2.me/theorems/f93c76c4-325e-4f6a-a50d-87bf4c59c225
-- title:
--   `BookProof.ChapterNumericalRangeSemigroup.norm_cexp_le_of_re_le` {ω t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z.re ≤ ω) : ‖Complex.exp ((t : ℂ) * z)‖ ≤ Real.exp (ω * t)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeSemigroup`.
--
--   `BookProof.ChapterNumericalRangeSemigroup.norm_cexp_le_of_re_le` {ω t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z.re ≤ ω) : ‖Complex.exp ((t : ℂ) * z)‖ ≤ Real.exp (ω * t)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeSemigroup.norm_cexp_le_of_re_le`.

-- Generated from ChapterNumericalRangeSemigroup.lean — theorem BookProof.ChapterNumericalRangeSemigroup.norm_cexp_le_of_re_le
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
open BookProof.ChapterNumericalRangeSemigroup


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterNumericalRangeSemigroup.norm_cexp_le_of_re_le {ω t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z.re ≤ ω) :
    ‖Complex.exp ((t : ℂ) * z)‖ ≤ Real.exp (ω * t) := by sorry
