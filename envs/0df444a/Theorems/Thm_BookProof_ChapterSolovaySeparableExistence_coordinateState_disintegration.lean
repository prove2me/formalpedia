-- Prove2me | Theorems.Thm_BookProof_ChapterSolovaySeparableExistence_coordinateState_disintegration
-- name    : BookProof.ChapterSolovaySeparableExistence.coordinateState_disintegration
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:45:56.905569+00:00
-- url     : https://prove2.me/theorems/37b6916e-a7fb-4898-868a-7516921343f5
-- title:
--   `BookProof.ChapterSolovaySeparableExistence.coordinateState_disintegration` (N : ℕ) (μ : Measure (CoordinateSpace N)) [IsFiniteMeasure μ] : ∃ κ : Kernel (Fin N → ℝ) CoordinateTail,
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolovaySeparableExistence`.
--
--   `BookProof.ChapterSolovaySeparableExistence.coordinateState_disintegration` (N : ℕ) (μ : Measure (CoordinateSpace N)) [IsFiniteMeasure μ] : ∃ κ : Kernel (Fin N → ℝ) CoordinateTail, IsMarkovKernel κ ∧ μ.fst ⊗ₘ κ = μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolovaySeparableExistence.coordinateState_disintegration`.

-- Generated from ChapterSolovaySeparableExistence.lean — theorem BookProof.ChapterSolovaySeparableExistence.coordinateState_disintegration
import Definitions.Def_ChapterSolovayCoordinates
import Mathlib
import Definitions.Def_ChapterSolovaySeparableExistence


noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterSolovayCoordinates

theorem BookProof.ChapterSolovaySeparableExistence.coordinateState_disintegration (N : ℕ) (μ : Measure (CoordinateSpace N))
    [IsFiniteMeasure μ] :
    ∃ κ : Kernel (Fin N → ℝ) CoordinateTail, IsMarkovKernel κ ∧ μ.fst ⊗ₘ κ = μ := by sorry
