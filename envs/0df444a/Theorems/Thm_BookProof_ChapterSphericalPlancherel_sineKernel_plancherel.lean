-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalPlancherel_sineKernel_plancherel
-- name    : BookProof.ChapterSphericalPlancherel.sineKernel_plancherel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:22:14.377968+00:00
-- url     : https://prove2.me/theorems/f41d8d69-355e-4551-96ef-11f5be2aed9b
-- title:
--   `BookProof.ChapterSphericalPlancherel.sineKernel_plancherel` (G : 𝓢(ℝ, ℂ)) (hodd : ∀ x, G (-x) = -G x) : ∫ p in Ioi (0 : ℝ), ‖sineKernelTransform (⇑G) p‖ ^ 2 = (π / 2) * ∫ x...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalPlancherel`.
--
--   `BookProof.ChapterSphericalPlancherel.sineKernel_plancherel` (G : 𝓢(ℝ, ℂ)) (hodd : ∀ x, G (-x) = -G x) : ∫ p in Ioi (0 : ℝ), ‖sineKernelTransform (⇑G) p‖ ^ 2 = (π / 2) * ∫ x in Ioi (0 : ℝ), ‖G x‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalPlancherel.sineKernel_plancherel`.

-- Generated from ChapterSphericalPlancherel.lean — theorem BookProof.ChapterSphericalPlancherel.sineKernel_plancherel
import Definitions.Def_ChapterSphericalBessel
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
open BookProof.ChapterSphericalPlancherel



open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalPlancherel.sineKernel_plancherel (G : 𝓢(ℝ, ℂ)) (hodd : ∀ x, G (-x) = -G x) :
    ∫ p in Ioi (0 : ℝ), ‖sineKernelTransform (⇑G) p‖ ^ 2
      = (π / 2) * ∫ x in Ioi (0 : ℝ), ‖G x‖ ^ 2 := by sorry
