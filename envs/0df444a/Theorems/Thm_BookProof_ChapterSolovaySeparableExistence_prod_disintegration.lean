-- Prove2me | Theorems.Thm_BookProof_ChapterSolovaySeparableExistence_prod_disintegration
-- name    : BookProof.ChapterSolovaySeparableExistence.prod_disintegration
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:46:02.762503+00:00
-- url     : https://prove2.me/theorems/e527e215-0f8d-4b54-aad5-e117e2bfaeaf
-- title:
--   `BookProof.ChapterSolovaySeparableExistence.prod_disintegration` {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] (μ : Measure (X × Y)) [Is
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolovaySeparableExistence`.
--
--   `BookProof.ChapterSolovaySeparableExistence.prod_disintegration` {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] (μ : Measure (X × Y)) [IsFiniteMeasure μ] : ∃ κ : Kernel X Y, IsMarkovKernel κ ∧ μ.fst ⊗ₘ κ = μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolovaySeparableExistence.prod_disintegration`.

-- Generated from ChapterSolovaySeparableExistence.lean — theorem BookProof.ChapterSolovaySeparableExistence.prod_disintegration
import Definitions.Def_ChapterSolovayCoordinates
import Mathlib
import Definitions.Def_ChapterSolovaySeparableExistence


noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterSolovayCoordinates

theorem BookProof.ChapterSolovaySeparableExistence.prod_disintegration {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] (μ : Measure (X × Y)) [IsFiniteMeasure μ] :
    ∃ κ : Kernel X Y, IsMarkovKernel κ ∧ μ.fst ⊗ₘ κ = μ := by sorry
