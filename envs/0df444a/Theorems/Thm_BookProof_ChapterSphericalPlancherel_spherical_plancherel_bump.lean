-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalPlancherel_spherical_plancherel_bump
-- name    : BookProof.ChapterSphericalPlancherel.spherical_plancherel_bump
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:22:43.119183+00:00
-- url     : https://prove2.me/theorems/8a0ee72e-369d-4906-9dee-d7453e9c8bd6
-- title:
--   `BookProof.ChapterSphericalPlancherel.spherical_plancherel_bump` : ∫ p in Ioi (0 : ℝ), ‖sphericalTransform (fun r : ℝ => oddBump r / (r : ℂ)) p‖ ^ 2 * p ^ 2 = ∫ r in Ioi (0 : ℝ), ‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalPlancherel`.
--
--   `BookProof.ChapterSphericalPlancherel.spherical_plancherel_bump` : ∫ p in Ioi (0 : ℝ), ‖sphericalTransform (fun r : ℝ => oddBump r / (r : ℂ)) p‖ ^ 2 * p ^ 2 = ∫ r in Ioi (0 : ℝ), ‖oddBump r / (r : ℂ)‖ ^ 2 * r ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalPlancherel.spherical_plancherel_bump`.

-- Generated from ChapterSphericalPlancherel.lean — theorem BookProof.ChapterSphericalPlancherel.spherical_plancherel_bump
import Definitions.Def_ChapterSphericalBessel
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
open BookProof.ChapterSphericalPlancherel



open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalPlancherel.spherical_plancherel_bump :
    ∫ p in Ioi (0 : ℝ), ‖sphericalTransform (fun r : ℝ => oddBump r / (r : ℂ)) p‖ ^ 2 * p ^ 2
      = ∫ r in Ioi (0 : ℝ), ‖oddBump r / (r : ℂ)‖ ^ 2 * r ^ 2 := by sorry
