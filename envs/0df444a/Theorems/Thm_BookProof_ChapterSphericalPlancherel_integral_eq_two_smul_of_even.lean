-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalPlancherel_integral_eq_two_smul_of_even
-- name    : BookProof.ChapterSphericalPlancherel.integral_eq_two_smul_of_even
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:20:43.12941+00:00
-- url     : https://prove2.me/theorems/34028ff4-59ab-4687-9a91-5450eaa888ff
-- title:
--   `BookProof.ChapterSphericalPlancherel.integral_eq_two_smul_of_even` {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) (h : ∀ x, f (-x) = f x) (hf : Integrable f) : ∫
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalPlancherel`.
--
--   `BookProof.ChapterSphericalPlancherel.integral_eq_two_smul_of_even` {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) (h : ∀ x, f (-x) = f x) (hf : Integrable f) : ∫ x : ℝ, f x = (2 : ℝ) • ∫ x in Ioi (0 : ℝ), f x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalPlancherel.integral_eq_two_smul_of_even`.

-- Generated from ChapterSphericalPlancherel.lean — theorem BookProof.ChapterSphericalPlancherel.integral_eq_two_smul_of_even
import Definitions.Def_ChapterSphericalBessel
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
open BookProof.ChapterSphericalPlancherel



open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalPlancherel.integral_eq_two_smul_of_even {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (h : ∀ x, f (-x) = f x) (hf : Integrable f) :
    ∫ x : ℝ, f x = (2 : ℝ) • ∫ x in Ioi (0 : ℝ), f x := by sorry
