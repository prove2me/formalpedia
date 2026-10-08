-- Prove2me | Theorems.Thm_BookProof_ChapterAngularMomentum_circHarm_rotate
-- name    : BookProof.ChapterAngularMomentum.circHarm_rotate
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:19:28.296242+00:00
-- url     : https://prove2.me/theorems/5dc01f9b-9e11-427e-9490-1131bf207819
-- title:
--   `BookProof.ChapterAngularMomentum.circHarm_rotate` (μ : ℕ) (t : ℝ) (z : ℂ) : circHarm μ (Complex.exp ((t : ℂ) * Complex.I) * z) = Complex.exp ((μ : ℂ) * (t : ℂ) * Complex.I) * circ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAngularMomentum`.
--
--   `BookProof.ChapterAngularMomentum.circHarm_rotate` (μ : ℕ) (t : ℝ) (z : ℂ) : circHarm μ (Complex.exp ((t : ℂ) * Complex.I) * z) = Complex.exp ((μ : ℂ) * (t : ℂ) * Complex.I) * circHarm μ z
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAngularMomentum.circHarm_rotate`.

-- Generated from ChapterAngularMomentum.lean — theorem BookProof.ChapterAngularMomentum.circHarm_rotate
import Mathlib
import Definitions.Def_ChapterAngularMomentum
open BookProof.ChapterAngularMomentum



open Complex

theorem BookProof.ChapterAngularMomentum.circHarm_rotate (μ : ℕ) (t : ℝ) (z : ℂ) :
    circHarm μ (Complex.exp ((t : ℂ) * Complex.I) * z)
      = Complex.exp ((μ : ℂ) * (t : ℂ) * Complex.I) * circHarm μ z := by sorry
