-- Prove2me | Theorems.Thm_BookProof_ChapterBornMeasure_isProbabilityMeasure_bornMeasure_isometry
-- name    : BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure_isometry
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:07:03.777082+00:00
-- url     : https://prove2.me/theorems/1bd01b47-20b3-4224-8600-ab5debcd73b8
-- title:
--   `BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure_isometry` (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (psi : Lp ℂ 2 μ) (hpsi : ‖psi‖ = 1) : IsProbabilityMeasure...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBornMeasure`.
--
--   `BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure_isometry` (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ) (psi : Lp ℂ 2 μ) (hpsi : ‖psi‖ = 1) : IsProbabilityMeasure (bornMeasure (U psi))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure_isometry`.

-- Generated from ChapterBornMeasure.lean — theorem BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure_isometry
import Mathlib
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterBornMeasure


open MeasureTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem BookProof.ChapterBornMeasure.isProbabilityMeasure_bornMeasure_isometry (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (psi : Lp ℂ 2 μ) (hpsi : ‖psi‖ = 1) : IsProbabilityMeasure (bornMeasure (U psi)) := by sorry
