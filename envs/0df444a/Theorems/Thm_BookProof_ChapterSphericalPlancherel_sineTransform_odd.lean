-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalPlancherel_sineTransform_odd
-- name    : BookProof.ChapterSphericalPlancherel.sineTransform_odd
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:21:59.519096+00:00
-- url     : https://prove2.me/theorems/658ed86f-7050-4613-b275-5d7fc7fcbe9d
-- title:
--   `BookProof.ChapterSphericalPlancherel.sineTransform_odd` (G : ℝ → ℂ) (w : ℝ) : sineTransform G (-w) = -sineTransform G w
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalPlancherel`.
--
--   `BookProof.ChapterSphericalPlancherel.sineTransform_odd` (G : ℝ → ℂ) (w : ℝ) : sineTransform G (-w) = -sineTransform G w
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalPlancherel.sineTransform_odd`.

-- Generated from ChapterSphericalPlancherel.lean — theorem BookProof.ChapterSphericalPlancherel.sineTransform_odd
import Definitions.Def_ChapterSphericalBessel
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
open BookProof.ChapterSphericalPlancherel



open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalPlancherel.sineTransform_odd (G : ℝ → ℂ) (w : ℝ) :
    sineTransform G (-w) = -sineTransform G w := by sorry
