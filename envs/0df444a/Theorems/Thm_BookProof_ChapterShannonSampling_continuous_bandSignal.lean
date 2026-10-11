-- Prove2me | Theorems.Thm_BookProof_ChapterShannonSampling_continuous_bandSignal
-- name    : BookProof.ChapterShannonSampling.continuous_bandSignal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:24:08.95059+00:00
-- url     : https://prove2.me/theorems/b8253e30-26b2-4f74-a401-f6e6ecae0ff1
-- title:
--   `BookProof.ChapterShannonSampling.continuous_bandSignal` (F : AddCircle T → ℂ) (hF : IntegrableOn (fun ξ : ℝ => F ξ) (Ioc (-(T / 2)) (-(T / 2) + T)) volume) : Continuous (bandSigna
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShannonSampling`.
--
--   `BookProof.ChapterShannonSampling.continuous_bandSignal` (F : AddCircle T → ℂ) (hF : IntegrableOn (fun ξ : ℝ => F ξ) (Ioc (-(T / 2)) (-(T / 2) + T)) volume) : Continuous (bandSignal (T := T) F)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterShannonSampling.continuous_bandSignal`.

-- Generated from ChapterShannonSampling.lean — theorem BookProof.ChapterShannonSampling.continuous_bandSignal
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling



open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

theorem BookProof.ChapterShannonSampling.continuous_bandSignal (F : AddCircle T → ℂ)
    (hF : IntegrableOn (fun ξ : ℝ => F ξ) (Ioc (-(T / 2)) (-(T / 2) + T)) volume) :
    Continuous (bandSignal (T := T) F) := by sorry
