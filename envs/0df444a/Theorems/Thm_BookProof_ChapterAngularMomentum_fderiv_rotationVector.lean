-- Prove2me | Theorems.Thm_BookProof_ChapterAngularMomentum_fderiv_rotationVector
-- name    : BookProof.ChapterAngularMomentum.fderiv_rotationVector
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:19:00.66166+00:00
-- url     : https://prove2.me/theorems/586ded9f-4b93-4016-86b1-fd365b38ccf6
-- title:
--   `BookProof.ChapterAngularMomentum.fderiv_rotationVector` (u : ℂ → ℂ) (z : ℂ) : fderiv ℝ u z (Complex.I * z) = z.re * fderiv ℝ u z Complex.I - z.im * fderiv ℝ u z 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAngularMomentum`.
--
--   `BookProof.ChapterAngularMomentum.fderiv_rotationVector` (u : ℂ → ℂ) (z : ℂ) : fderiv ℝ u z (Complex.I * z) = z.re * fderiv ℝ u z Complex.I - z.im * fderiv ℝ u z 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAngularMomentum.fderiv_rotationVector`.

-- Generated from ChapterAngularMomentum.lean — theorem BookProof.ChapterAngularMomentum.fderiv_rotationVector
import Mathlib
import Definitions.Def_ChapterAngularMomentum
open BookProof.ChapterAngularMomentum



open Complex

theorem BookProof.ChapterAngularMomentum.fderiv_rotationVector (u : ℂ → ℂ) (z : ℂ) :
    fderiv ℝ u z (Complex.I * z)
      = z.re * fderiv ℝ u z Complex.I - z.im * fderiv ℝ u z 1 := by sorry
