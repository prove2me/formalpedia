-- Prove2me | Theorems.Thm_BookProof_QuantumGravityHalfDensity_halfDensityUnitary_symm_apply
-- name    : BookProof.QuantumGravityHalfDensity.halfDensityUnitary_symm_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:58:34.400337+00:00
-- url     : https://prove2.me/theorems/9829421f-d1b4-45c3-b7c4-a629f9e05c07
-- title:
--   `BookProof.QuantumGravityHalfDensity.halfDensityUnitary_symm_apply` (h : Lp ℂ 2 qgSrcMeasure) : (halfDensityUnitary.symm h : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] fun e => (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityHalfDensity`.
--
--   `BookProof.QuantumGravityHalfDensity.halfDensityUnitary_symm_apply` (h : Lp ℂ 2 qgSrcMeasure) : (halfDensityUnitary.symm h : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] fun e => (h : ℝ → ℂ) (Real.sqrt e)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityHalfDensity.halfDensityUnitary_symm_apply`.

-- Generated from ChapterQuantumGravityHalfDensity.lean — theorem BookProof.QuantumGravityHalfDensity.halfDensityUnitary_symm_apply
import Mathlib
import Definitions.Def_ChapterQuantumGravityHalfDensity
open BookProof.QuantumGravityHalfDensity



open MeasureTheory Set Filter
open scoped ENNReal

theorem BookProof.QuantumGravityHalfDensity.halfDensityUnitary_symm_apply (h : Lp ℂ 2 qgSrcMeasure) :
    (halfDensityUnitary.symm h : ℝ → ℂ)
      =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] fun e => (h : ℝ → ℂ) (Real.sqrt e) := by sorry
