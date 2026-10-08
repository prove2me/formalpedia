-- Prove2me | Theorems.Thm_BookProof_ChapterAngularMomentum_circHarm_angularMomentum_eigen
-- name    : BookProof.ChapterAngularMomentum.circHarm_angularMomentum_eigen
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:19:44.921359+00:00
-- url     : https://prove2.me/theorems/9b922fcf-9bc7-4030-ac13-b2b94d3fa19c
-- title:
--   `BookProof.ChapterAngularMomentum.circHarm_angularMomentum_eigen` (μ : ℕ) {z : ℂ} (hz : z ≠ 0) : -Complex.I * (z.re * fderiv ℝ (circHarm μ) z Complex.I - z.im * fderiv ℝ (circHarm
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAngularMomentum`.
--
--   `BookProof.ChapterAngularMomentum.circHarm_angularMomentum_eigen` (μ : ℕ) {z : ℂ} (hz : z ≠ 0) : -Complex.I * (z.re * fderiv ℝ (circHarm μ) z Complex.I - z.im * fderiv ℝ (circHarm μ) z 1) = (μ : ℂ) * circHarm μ z
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAngularMomentum.circHarm_angularMomentum_eigen`.

-- Generated from ChapterAngularMomentum.lean — theorem BookProof.ChapterAngularMomentum.circHarm_angularMomentum_eigen
import Mathlib
import Definitions.Def_ChapterAngularMomentum
open BookProof.ChapterAngularMomentum



open Complex

theorem BookProof.ChapterAngularMomentum.circHarm_angularMomentum_eigen (μ : ℕ) {z : ℂ} (hz : z ≠ 0) :
    -Complex.I * (z.re * fderiv ℝ (circHarm μ) z Complex.I
        - z.im * fderiv ℝ (circHarm μ) z 1)
      = (μ : ℂ) * circHarm μ z := by sorry
