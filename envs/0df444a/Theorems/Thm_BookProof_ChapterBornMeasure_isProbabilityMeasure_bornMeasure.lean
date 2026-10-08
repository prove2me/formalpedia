-- Prove2me | Theorems.Thm_BookProof_ChapterBornMeasure_isProbabilityMeasure_bornMeasure
-- name    : BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:07:26.35479+00:00
-- url     : https://prove2.me/theorems/ad6d4571-47bd-4fd9-8c19-07c4f9482943
-- title:
--   `BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure` (psi : Lp ℂ 2 μ) (hpsi : ‖psi‖ = 1) : IsProbabilityMeasure (bornMeasure psi)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBornMeasure`.
--
--   `BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure` (psi : Lp ℂ 2 μ) (hpsi : ‖psi‖ = 1) : IsProbabilityMeasure (bornMeasure psi)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure`.

-- Generated from ChapterBornMeasure.lean — theorem BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure
import Mathlib
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterBornMeasure


open MeasureTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure (psi : Lp ℂ 2 μ) (hpsi : ‖psi‖ = 1) :
    IsProbabilityMeasure (bornMeasure psi) := by sorry
