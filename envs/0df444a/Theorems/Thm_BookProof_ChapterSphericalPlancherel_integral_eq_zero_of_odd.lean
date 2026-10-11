-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalPlancherel_integral_eq_zero_of_odd
-- name    : BookProof.ChapterSphericalPlancherel.integral_eq_zero_of_odd
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:20:31.832276+00:00
-- url     : https://prove2.me/theorems/a1b5c34c-b5fb-4213-bc1b-13260c413f97
-- title:
--   `BookProof.ChapterSphericalPlancherel.integral_eq_zero_of_odd` {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) (h : ∀ x, f (-x) = -f x) : ∫ x : ℝ, f x = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalPlancherel`.
--
--   `BookProof.ChapterSphericalPlancherel.integral_eq_zero_of_odd` {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) (h : ∀ x, f (-x) = -f x) : ∫ x : ℝ, f x = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalPlancherel.integral_eq_zero_of_odd`.

-- Generated from ChapterSphericalPlancherel.lean — theorem BookProof.ChapterSphericalPlancherel.integral_eq_zero_of_odd
import Definitions.Def_ChapterSphericalBessel
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
open BookProof.ChapterSphericalPlancherel



open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalPlancherel.integral_eq_zero_of_odd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (h : ∀ x, f (-x) = -f x) : ∫ x : ℝ, f x = 0 := by sorry
