-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalPlancherel_integral_eq_two_mul_of_even_real
-- name    : BookProof.ChapterSphericalPlancherel.integral_eq_two_mul_of_even_real
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:20:49.353983+00:00
-- url     : https://prove2.me/theorems/045deced-6a5e-4304-9d31-9d13edd60183
-- title:
--   `BookProof.ChapterSphericalPlancherel.integral_eq_two_mul_of_even_real` (h : ℝ → ℝ) (he : ∀ x, h (-x) = h x) : ∫ x : ℝ, h x = 2 * ∫ x in Ioi (0 : ℝ), h x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalPlancherel`.
--
--   `BookProof.ChapterSphericalPlancherel.integral_eq_two_mul_of_even_real` (h : ℝ → ℝ) (he : ∀ x, h (-x) = h x) : ∫ x : ℝ, h x = 2 * ∫ x in Ioi (0 : ℝ), h x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalPlancherel.integral_eq_two_mul_of_even_real`.

-- Generated from ChapterSphericalPlancherel.lean — theorem BookProof.ChapterSphericalPlancherel.integral_eq_two_mul_of_even_real
import Definitions.Def_ChapterSphericalBessel
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
open BookProof.ChapterSphericalPlancherel



open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalPlancherel.integral_eq_two_mul_of_even_real (h : ℝ → ℝ) (he : ∀ x, h (-x) = h x) :
    ∫ x : ℝ, h x = 2 * ∫ x in Ioi (0 : ℝ), h x := by sorry
