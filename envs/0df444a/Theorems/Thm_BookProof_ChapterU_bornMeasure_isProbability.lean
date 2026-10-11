-- Prove2me | Theorems.Thm_BookProof_ChapterU_bornMeasure_isProbability
-- name    : BookProof.ChapterU.bornMeasure_isProbability
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:29:00.183115+00:00
-- url     : https://prove2.me/theorems/fd22ecdd-e5a3-4bae-bfd3-67c0668f0e82
-- title:
--   `BookProof.ChapterU.bornMeasure_isProbability` (Ψ : X → ℂ) (μ : Measure X) (hΨ : MemLp Ψ 2 μ) (hnorm : ∫ x, ‖Ψ x‖ ^ 2 ∂μ = 1) : IsProbabilityMeasure (bornMeasure Ψ μ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterU`.
--
--   `BookProof.ChapterU.bornMeasure_isProbability` (Ψ : X → ℂ) (μ : Measure X) (hΨ : MemLp Ψ 2 μ) (hnorm : ∫ x, ‖Ψ x‖ ^ 2 ∂μ = 1) : IsProbabilityMeasure (bornMeasure Ψ μ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterU.bornMeasure_isProbability`.

-- Generated from ChapterU.lean — theorem BookProof.ChapterU.bornMeasure_isProbability
import Mathlib
import Definitions.Def_ChapterU
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterBornMeasure
open BookProof.ChapterU


open MeasureTheory
open scoped ENNReal ProbabilityTheory TensorProduct

variable {X : Type*} [MeasurableSpace X]

theorem BookProof.ChapterU.bornMeasure_isProbability (Ψ : X → ℂ) (μ : Measure X)
    (hΨ : MemLp Ψ 2 μ) (hnorm : ∫ x, ‖Ψ x‖ ^ 2 ∂μ = 1) :
    IsProbabilityMeasure (bornMeasure Ψ μ) := by sorry
