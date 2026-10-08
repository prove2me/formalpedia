-- Prove2me | Theorems.Thm_BookProof_energyTransform_symm
-- name    : BookProof.energyTransform_symm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:09:27.761984+00:00
-- url     : https://prove2.me/theorems/c07c7728-87b4-4530-b9a7-c3b0cb23a466
-- title:
--   `BookProof.energyTransform_symm` (Θ : (Lp F 2 (volume : Measure E)) ≃ₗᵢ[ℝ] P) (fourierTime : (Lp F 2 (volume : Measure E)) ≃ₗᵢ[ℝ] (Lp F 2 (volume : Measure E))) : (energyTransform
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4`.
--
--   `BookProof.energyTransform_symm` (Θ : (Lp F 2 (volume : Measure E)) ≃ₗᵢ[ℝ] P) (fourierTime : (Lp F 2 (volume : Measure E)) ≃ₗᵢ[ℝ] (Lp F 2 (volume : Measure E))) : (energyTransform E F Θ fourierTime).symm = conjugateₗᵢ Θ fourierTime.symm
--
--   Formalization note: Lean 4 identifier `BookProof.energyTransform_symm`.

-- Generated from ChapterA4.lean — theorem BookProof.energyTransform_symm
import Mathlib
import Definitions.Def_ChapterA4
open BookProof



open MeasureTheory




variable {R E E' : Type*} [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E'] [Module R E] [Module R E']

variable (E F : Type*) [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

theorem BookProof.energyTransform_symm
    (Θ : (Lp F 2 (volume : Measure E)) ≃ₗᵢ[ℝ] P)
    (fourierTime : (Lp F 2 (volume : Measure E)) ≃ₗᵢ[ℝ] (Lp F 2 (volume : Measure E))) :
    (energyTransform E F Θ fourierTime).symm = conjugateₗᵢ Θ fourierTime.symm := by sorry
