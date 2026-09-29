-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_volume_preservation_constraint
-- name    : BookProof.NavierStokesFlow.volume_preservation_constraint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:31:04.535001+00:00
-- url     : https://prove2.me/theorems/a496504d-fa5f-43c2-b95b-086ce1f60267
-- title:
--   The Lean 4 theorem `volume_preservation_constraint` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `volume_preservation_constraint` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.volume_preservation_constraint
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

theorem BookProof.NavierStokesFlow.volume_preservation_constraint {d : ℕ} (f : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))
    (hdet : LinearMap.det f = 1) (s : Set (Fin d → ℝ)) :
    MeasureTheory.volume (f '' s) = MeasureTheory.volume s := by sorry
