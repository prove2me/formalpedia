-- Prove2me | Theorems.Thm_BookProof_QuantumGravityHalfDensity_halfDensityUnitary_apply
-- name    : BookProof.QuantumGravityHalfDensity.halfDensityUnitary_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:57:37.698779+00:00
-- url     : https://prove2.me/theorems/7f84cc78-6442-4f5b-aa0f-48bc191efcad
-- title:
--   `BookProof.QuantumGravityHalfDensity.halfDensityUnitary_apply` (g : Lp ℂ 2 (volume.restrict (Set.Ioi (0 : ℝ)))) : (halfDensityUnitary g : ℝ → ℂ) =ᵐ[qgSrcMeasure] fun y => (g : ℝ →
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityHalfDensity`.
--
--   `BookProof.QuantumGravityHalfDensity.halfDensityUnitary_apply` (g : Lp ℂ 2 (volume.restrict (Set.Ioi (0 : ℝ)))) : (halfDensityUnitary g : ℝ → ℂ) =ᵐ[qgSrcMeasure] fun y => (g : ℝ → ℂ) (y ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityHalfDensity.halfDensityUnitary_apply`.

-- Generated from ChapterQuantumGravityHalfDensity.lean — theorem BookProof.QuantumGravityHalfDensity.halfDensityUnitary_apply
import Mathlib
import Definitions.Def_ChapterQuantumGravityHalfDensity
open BookProof.QuantumGravityHalfDensity



open MeasureTheory Set Filter
open scoped ENNReal

theorem BookProof.QuantumGravityHalfDensity.halfDensityUnitary_apply (g : Lp ℂ 2 (volume.restrict (Set.Ioi (0 : ℝ)))) :
    (halfDensityUnitary g : ℝ → ℂ) =ᵐ[qgSrcMeasure] fun y => (g : ℝ → ℂ) (y ^ 2) := by sorry
