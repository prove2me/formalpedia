-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalPlancherel_fourier_odd_eq
-- name    : BookProof.ChapterSphericalPlancherel.fourier_odd_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:21:12.396004+00:00
-- url     : https://prove2.me/theorems/b906f6b7-28ac-49a7-9e6d-abc1738394d8
-- title:
--   `BookProof.ChapterSphericalPlancherel.fourier_odd_eq` (G : ℝ → ℂ) (hG : Integrable G) (hodd : ∀ x, G (-x) = -G x) (w : ℝ) : 𝓕 G w = -(2 * Complex.I) * sineTransform G w
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalPlancherel`.
--
--   `BookProof.ChapterSphericalPlancherel.fourier_odd_eq` (G : ℝ → ℂ) (hG : Integrable G) (hodd : ∀ x, G (-x) = -G x) (w : ℝ) : 𝓕 G w = -(2 * Complex.I) * sineTransform G w
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalPlancherel.fourier_odd_eq`.

-- Generated from ChapterSphericalPlancherel.lean — theorem BookProof.ChapterSphericalPlancherel.fourier_odd_eq
import Definitions.Def_ChapterSphericalBessel
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
open BookProof.ChapterSphericalPlancherel



open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalPlancherel.fourier_odd_eq (G : ℝ → ℂ) (hG : Integrable G) (hodd : ∀ x, G (-x) = -G x) (w : ℝ) :
    𝓕 G w = -(2 * Complex.I) * sineTransform G w := by sorry
