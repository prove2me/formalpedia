-- Prove2me | Theorems.Thm_BookProof_ChapterBornMeasure_condProb_of_bounded_dynamics
-- name    : BookProof.ChapterBornMeasure.condProb_of_bounded_dynamics
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:07:27.755015+00:00
-- url     : https://prove2.me/theorems/16ef55be-aa22-4d65-b7ac-87531dbd0f9b
-- title:
--   `BookProof.ChapterBornMeasure.condProb_of_bounded_dynamics` (H : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hH : IsSelfAdjoint H) (psi : Lp ℂ 2 μ) (hpsi : ‖psi‖ = 1) (t : ℝ) : IsProbabilityMeasure
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBornMeasure`.
--
--   `BookProof.ChapterBornMeasure.condProb_of_bounded_dynamics` (H : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hH : IsSelfAdjoint H) (psi : Lp ℂ 2 μ) (hpsi : ‖psi‖ = 1) (t : ℝ) : IsProbabilityMeasure (bornMeasure (evolve H t psi)) ∧ bornMeasure (evolve H t psi) ≪ μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBornMeasure.condProb_of_bounded_dynamics`.

-- Generated from ChapterBornMeasure.lean — theorem BookProof.ChapterBornMeasure.condProb_of_bounded_dynamics
import Mathlib
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterBornMeasure


open MeasureTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem BookProof.ChapterBornMeasure.condProb_of_bounded_dynamics (H : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hH : IsSelfAdjoint H)
    (psi : Lp ℂ 2 μ) (hpsi : ‖psi‖ = 1) (t : ℝ) :
    IsProbabilityMeasure (bornMeasure (evolve H t psi)) ∧
      bornMeasure (evolve H t psi) ≪ μ := by sorry
