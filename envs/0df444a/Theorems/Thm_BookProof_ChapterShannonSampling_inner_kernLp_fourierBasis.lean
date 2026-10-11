-- Prove2me | Theorems.Thm_BookProof_ChapterShannonSampling_inner_kernLp_fourierBasis
-- name    : BookProof.ChapterShannonSampling.inner_kernLp_fourierBasis
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:23:10.959758+00:00
-- url     : https://prove2.me/theorems/14ac052e-f346-404f-8121-3385f56800a3
-- title:
--   `BookProof.ChapterShannonSampling.inner_kernLp_fourierBasis` (x : ℝ) (n : ℤ) : inner ℂ (kernLp (T := T) x) (fourierBasis (T := T) n) = (sinc (T * x + n) : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShannonSampling`.
--
--   `BookProof.ChapterShannonSampling.inner_kernLp_fourierBasis` (x : ℝ) (n : ℤ) : inner ℂ (kernLp (T := T) x) (fourierBasis (T := T) n) = (sinc (T * x + n) : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterShannonSampling.inner_kernLp_fourierBasis`.

-- Generated from ChapterShannonSampling.lean — theorem BookProof.ChapterShannonSampling.inner_kernLp_fourierBasis
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling



open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

theorem BookProof.ChapterShannonSampling.inner_kernLp_fourierBasis (x : ℝ) (n : ℤ) :
    inner ℂ (kernLp (T := T) x) (fourierBasis (T := T) n) = (sinc (T * x + n) : ℝ) := by sorry
