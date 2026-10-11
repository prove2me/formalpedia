-- Prove2me | Theorems.Thm_BookProof_ChapterShannonSampling_inner_kernLp_apply
-- name    : BookProof.ChapterShannonSampling.inner_kernLp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:22:56.457027+00:00
-- url     : https://prove2.me/theorems/5b7842d2-d6e4-4f7c-abb8-de91a972c105
-- title:
--   `BookProof.ChapterShannonSampling.inner_kernLp_apply` (F : Lp ℂ 2 (haarAddCircle (T := T))) (x : ℝ) : inner ℂ (kernLp (T := T) x) F = ∫ z : AddCircle T, conj (kern (T := T) x z) *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShannonSampling`.
--
--   `BookProof.ChapterShannonSampling.inner_kernLp_apply` (F : Lp ℂ 2 (haarAddCircle (T := T))) (x : ℝ) : inner ℂ (kernLp (T := T) x) F = ∫ z : AddCircle T, conj (kern (T := T) x z) * F z ∂haarAddCircle
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterShannonSampling.inner_kernLp_apply`.

-- Generated from ChapterShannonSampling.lean — theorem BookProof.ChapterShannonSampling.inner_kernLp_apply
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling



open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

theorem BookProof.ChapterShannonSampling.inner_kernLp_apply (F : Lp ℂ 2 (haarAddCircle (T := T))) (x : ℝ) :
    inner ℂ (kernLp (T := T) x) F
      = ∫ z : AddCircle T, conj (kern (T := T) x z) * F z ∂haarAddCircle := by sorry
