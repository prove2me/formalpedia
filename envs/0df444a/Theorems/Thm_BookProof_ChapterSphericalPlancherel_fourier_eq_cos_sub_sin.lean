-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalPlancherel_fourier_eq_cos_sub_sin
-- name    : BookProof.ChapterSphericalPlancherel.fourier_eq_cos_sub_sin
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:21:38.209362+00:00
-- url     : https://prove2.me/theorems/8ec4222d-5adb-4843-9105-2e5ce2331d5f
-- title:
--   `BookProof.ChapterSphericalPlancherel.fourier_eq_cos_sub_sin` (f : ℝ → ℂ) (w : ℝ) : 𝓕 f w = ∫ x : ℝ, ((Real.cos (2 * π * (x * w)) : ℂ) - (Real.sin (2 * π * (x * w)) : ℂ) *...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalPlancherel`.
--
--   `BookProof.ChapterSphericalPlancherel.fourier_eq_cos_sub_sin` (f : ℝ → ℂ) (w : ℝ) : 𝓕 f w = ∫ x : ℝ, ((Real.cos (2 * π * (x * w)) : ℂ) - (Real.sin (2 * π * (x * w)) : ℂ) * Complex.I) * f x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalPlancherel.fourier_eq_cos_sub_sin`.

-- Generated from ChapterSphericalPlancherel.lean — theorem BookProof.ChapterSphericalPlancherel.fourier_eq_cos_sub_sin
import Definitions.Def_ChapterSphericalBessel
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
open BookProof.ChapterSphericalPlancherel



open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalPlancherel.fourier_eq_cos_sub_sin (f : ℝ → ℂ) (w : ℝ) :
    𝓕 f w = ∫ x : ℝ, ((Real.cos (2 * π * (x * w)) : ℂ)
      - (Real.sin (2 * π * (x * w)) : ℂ) * Complex.I) * f x := by sorry
