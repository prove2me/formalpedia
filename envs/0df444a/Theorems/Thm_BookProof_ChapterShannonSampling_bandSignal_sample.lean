-- Prove2me | Theorems.Thm_BookProof_ChapterShannonSampling_bandSignal_sample
-- name    : BookProof.ChapterShannonSampling.bandSignal_sample
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:23:30.544153+00:00
-- url     : https://prove2.me/theorems/0621881f-97fe-4215-847f-7ea3eca63e4f
-- title:
--   `BookProof.ChapterShannonSampling.bandSignal_sample` (F : AddCircle T → ℂ) (n : ℤ) : bandSignal (T := T) F (-(n / T)) = (T : ℂ) * fourierCoeff F n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShannonSampling`.
--
--   `BookProof.ChapterShannonSampling.bandSignal_sample` (F : AddCircle T → ℂ) (n : ℤ) : bandSignal (T := T) F (-(n / T)) = (T : ℂ) * fourierCoeff F n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterShannonSampling.bandSignal_sample`.

-- Generated from ChapterShannonSampling.lean — theorem BookProof.ChapterShannonSampling.bandSignal_sample
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling



open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

theorem BookProof.ChapterShannonSampling.bandSignal_sample (F : AddCircle T → ℂ) (n : ℤ) :
    bandSignal (T := T) F (-(n / T)) = (T : ℂ) * fourierCoeff F n := by sorry
