-- Prove2me | Theorems.Thm_BookProof_ChapterSphericalPlancherel_sineKernelTransform_eq
-- name    : BookProof.ChapterSphericalPlancherel.sineKernelTransform_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T15:21:54.908978+00:00
-- url     : https://prove2.me/theorems/bc65f67a-6b6c-4224-a28f-63332dc9353a
-- title:
--   `BookProof.ChapterSphericalPlancherel.sineKernelTransform_eq` (G : ℝ → ℂ) (p : ℝ) : sineKernelTransform G p = sineTransform G ((2 * π)⁻¹ * p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSphericalPlancherel`.
--
--   `BookProof.ChapterSphericalPlancherel.sineKernelTransform_eq` (G : ℝ → ℂ) (p : ℝ) : sineKernelTransform G p = sineTransform G ((2 * π)⁻¹ * p)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSphericalPlancherel.sineKernelTransform_eq`.

-- Generated from ChapterSphericalPlancherel.lean — theorem BookProof.ChapterSphericalPlancherel.sineKernelTransform_eq
import Definitions.Def_ChapterSphericalBessel
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
open BookProof.ChapterSphericalPlancherel



open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

theorem BookProof.ChapterSphericalPlancherel.sineKernelTransform_eq (G : ℝ → ℂ) (p : ℝ) :
    sineKernelTransform G p = sineTransform G ((2 * π)⁻¹ * p) := by sorry
