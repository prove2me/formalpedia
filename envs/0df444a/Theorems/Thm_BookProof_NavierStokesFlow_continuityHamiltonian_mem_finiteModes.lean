-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_continuityHamiltonian_mem_finiteModes
-- name    : BookProof.NavierStokesFlow.continuityHamiltonian_mem_finiteModes
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:20:37.848714+00:00
-- url     : https://prove2.me/theorems/645c112d-86ce-487e-9f8c-1c3d3706a89c
-- title:
--   The Lean 4 theorem `continuityHamiltonian_mem_finiteModes` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `continuityHamiltonian_mem_finiteModes` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesEsa.lean

-- Generated from ChapterNavierStokesEsa.lean — theorem BookProof.NavierStokesFlow.continuityHamiltonian_mem_finiteModes
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow








open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

















variable {ι : Type*}









open BookProof.ChapterContinuityUnitaryInfinite

theorem BookProof.NavierStokesFlow.continuityHamiltonian_mem_finiteModes (v : LinfZ) {f : L2Z} (hf : f ∈ finiteModes) :
    continuityHamiltonian v f ∈ finiteModes := by sorry
