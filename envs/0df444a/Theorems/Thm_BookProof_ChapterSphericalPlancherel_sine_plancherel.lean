-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalPlancherel_sine_plancherel
-- name    : BookProof.ChapterSphericalPlancherel.sine_plancherel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:21:14.202045+00:00
-- url     : https://prove2.me/theorems/e82d1f80-29c6-41d4-a532-980f93055b25
-- title:
--   `BookProof.ChapterSphericalPlancherel.sine_plancherel` (G : 𝓢(ℝ, ℂ)) (hodd : ∀ x, G (-x) = -G x) : ∫ w in Ioi (0 : ℝ), ‖sineTransform (⇑G) w‖ ^ 2 = (1 / 4) * ∫ x in Ioi (0...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalPlancherel`.
--
--   `BookProof.ChapterSphericalPlancherel.sine_plancherel` (G : 𝓢(ℝ, ℂ)) (hodd : ∀ x, G (-x) = -G x) : ∫ w in Ioi (0 : ℝ), ‖sineTransform (⇑G) w‖ ^ 2 = (1 / 4) * ∫ x in Ioi (0 : ℝ), ‖G x‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalPlancherel.sine_plancherel`.

-- Generated from ChapterSphericalPlancherel.lean — theorem BookProof.ChapterSphericalPlancherel.sine_plancherel
import Definitions.Def_ChapterSphericalBessel
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
open BookProof.ChapterSphericalPlancherel



open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalPlancherel.sine_plancherel (G : 𝓢(ℝ, ℂ)) (hodd : ∀ x, G (-x) = -G x) :
    ∫ w in Ioi (0 : ℝ), ‖sineTransform (⇑G) w‖ ^ 2
      = (1 / 4) * ∫ x in Ioi (0 : ℝ), ‖G x‖ ^ 2 := by sorry
