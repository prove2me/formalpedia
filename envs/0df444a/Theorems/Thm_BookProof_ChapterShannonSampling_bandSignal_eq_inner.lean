-- Prove2me | Theorems.Thm_BookProof_ChapterShannonSampling_bandSignal_eq_inner
-- name    : BookProof.ChapterShannonSampling.bandSignal_eq_inner
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:22:59.231437+00:00
-- url     : https://prove2.me/theorems/7e149ad6-b46b-4a61-a53d-a460c03c7b72
-- title:
--   `BookProof.ChapterShannonSampling.bandSignal_eq_inner` (F : Lp ℂ 2 (haarAddCircle (T := T))) (x : ℝ) : bandSignal (T := T) (F : AddCircle T → ℂ) x = (T : ℂ) * inner ℂ (kernLp (T :=
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShannonSampling`.
--
--   `BookProof.ChapterShannonSampling.bandSignal_eq_inner` (F : Lp ℂ 2 (haarAddCircle (T := T))) (x : ℝ) : bandSignal (T := T) (F : AddCircle T → ℂ) x = (T : ℂ) * inner ℂ (kernLp (T := T) x) F
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterShannonSampling.bandSignal_eq_inner`.

-- Generated from ChapterShannonSampling.lean — theorem BookProof.ChapterShannonSampling.bandSignal_eq_inner
import Mathlib
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterShannonSampling



open MeasureTheory Complex AddCircle intervalIntegral Set
open scoped Real ComplexConjugate

variable {T : ℝ} [hT : Fact (0 < T)]

theorem BookProof.ChapterShannonSampling.bandSignal_eq_inner (F : Lp ℂ 2 (haarAddCircle (T := T))) (x : ℝ) :
    bandSignal (T := T) (F : AddCircle T → ℂ) x
      = (T : ℂ) * inner ℂ (kernLp (T := T) x) F := by sorry
