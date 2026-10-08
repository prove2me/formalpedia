-- Prove2me | Theorems.Thm_BookProof_ChapterBornMeasure_norm_evolve
-- name    : BookProof.ChapterBornMeasure.norm_evolve
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:29:50.010733+00:00
-- url     : https://prove2.me/theorems/e0b9900e-37c3-43f2-b56b-3b659e981d82
-- title:
--   `BookProof.ChapterBornMeasure.norm_evolve` (H : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hH : IsSelfAdjoint H) (t : ℝ) (psi : Lp ℂ 2 μ) : ‖evolve H t psi‖ = ‖psi‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBornMeasure`.
--
--   `BookProof.ChapterBornMeasure.norm_evolve` (H : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hH : IsSelfAdjoint H) (t : ℝ) (psi : Lp ℂ 2 μ) : ‖evolve H t psi‖ = ‖psi‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBornMeasure.norm_evolve`.

-- Generated from ChapterBornMeasure.lean — theorem BookProof.ChapterBornMeasure.norm_evolve
import Mathlib
import Definitions.Def_ChapterBornMeasure
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterBornMeasure


open MeasureTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem BookProof.ChapterBornMeasure.norm_evolve (H : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hH : IsSelfAdjoint H) (t : ℝ)
    (psi : Lp ℂ 2 μ) : ‖evolve H t psi‖ = ‖psi‖ := by sorry
