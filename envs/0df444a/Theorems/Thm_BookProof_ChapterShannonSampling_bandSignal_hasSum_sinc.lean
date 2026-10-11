-- Prove2me | Theorems.Thm_BookProof_ChapterShannonSampling_bandSignal_hasSum_sinc
-- name    : BookProof.ChapterShannonSampling.bandSignal_hasSum_sinc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:23:28.198059+00:00
-- url     : https://prove2.me/theorems/f3bbf0c5-bd46-4b4d-8711-94a5265a0ca2
-- title:
--   `BookProof.ChapterShannonSampling.bandSignal_hasSum_sinc` (F : Lp ℂ 2 (haarAddCircle (T := T))) (x : ℝ) : HasSum (fun n : ℤ => bandSignal (T := T) (F : AddCircle T → ℂ) (n / T) * (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShannonSampling`.
--
--   `BookProof.ChapterShannonSampling.bandSignal_hasSum_sinc` (F : Lp ℂ 2 (haarAddCircle (T := T))) (x : ℝ) : HasSum (fun n : ℤ => bandSignal (T := T) (F : AddCircle T → ℂ) (n / T) * (sinc (T * x - n) : ℝ)) (bandSignal (T := T) (F : AddCircle T → ℂ) x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterShannonSampling.bandSignal_hasSum_sinc`.

-- Generated from ChapterShannonSampling.lean — theorem BookProof.ChapterShannonSampling.bandSignal_hasSum_sinc
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling



open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

theorem BookProof.ChapterShannonSampling.bandSignal_hasSum_sinc (F : Lp ℂ 2 (haarAddCircle (T := T))) (x : ℝ) :
    HasSum (fun n : ℤ =>
        bandSignal (T := T) (F : AddCircle T → ℂ) (n / T) * (sinc (T * x - n) : ℝ))
      (bandSignal (T := T) (F : AddCircle T → ℂ) x) := by sorry
