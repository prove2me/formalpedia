-- Prove2me | Theorems.Thm_BookProof_ChapterShannonSampling_half_add_period
-- name    : BookProof.ChapterShannonSampling.half_add_period
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:22:18.838292+00:00
-- url     : https://prove2.me/theorems/df2a8391-e403-41d6-a06a-c23d342c0531
-- title:
--   `BookProof.ChapterShannonSampling.half_add_period` : -(T / 2) + T = T / 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShannonSampling`.
--
--   `BookProof.ChapterShannonSampling.half_add_period` : -(T / 2) + T = T / 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterShannonSampling.half_add_period`.

-- Generated from ChapterShannonSampling.lean — theorem BookProof.ChapterShannonSampling.half_add_period
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling



open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

omit hT in

theorem BookProof.ChapterShannonSampling.half_add_period : -(T / 2) + T = T / 2 := by sorry
