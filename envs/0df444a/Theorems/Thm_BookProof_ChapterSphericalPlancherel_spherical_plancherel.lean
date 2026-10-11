-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalPlancherel_spherical_plancherel
-- name    : BookProof.ChapterSphericalPlancherel.spherical_plancherel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:21:59.579423+00:00
-- url     : https://prove2.me/theorems/f998017f-92e6-4d14-8988-85e3f60e0483
-- title:
--   `BookProof.ChapterSphericalPlancherel.spherical_plancherel` (G : 𝓢(ℝ, ℂ)) (hodd : ∀ x, G (-x) = -G x) (f : ℝ → ℂ) (hf : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) * f r = G r) : ∫ p in...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalPlancherel`.
--
--   `BookProof.ChapterSphericalPlancherel.spherical_plancherel` (G : 𝓢(ℝ, ℂ)) (hodd : ∀ x, G (-x) = -G x) (f : ℝ → ℂ) (hf : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) * f r = G r) : ∫ p in Ioi (0 : ℝ), ‖sphericalTransform f p‖ ^ 2 * p ^ 2 = ∫ r in Ioi (0 : ℝ), ‖f r‖ ^ 2 * r ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalPlancherel.spherical_plancherel`.

-- Generated from ChapterSphericalPlancherel.lean — theorem BookProof.ChapterSphericalPlancherel.spherical_plancherel
import Definitions.Def_ChapterSphericalBessel
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
open BookProof.ChapterSphericalPlancherel



open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalPlancherel.spherical_plancherel (G : 𝓢(ℝ, ℂ)) (hodd : ∀ x, G (-x) = -G x)
    (f : ℝ → ℂ) (hf : ∀ r ∈ Ioi (0 : ℝ), (r : ℂ) * f r = G r) :
    ∫ p in Ioi (0 : ℝ), ‖sphericalTransform f p‖ ^ 2 * p ^ 2
      = ∫ r in Ioi (0 : ℝ), ‖f r‖ ^ 2 * r ^ 2 := by sorry
