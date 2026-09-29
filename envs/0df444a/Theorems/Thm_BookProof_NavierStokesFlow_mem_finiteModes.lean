-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_mem_finiteModes
-- name    : BookProof.NavierStokesFlow.mem_finiteModes
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:58:04.475471+00:00
-- url     : https://prove2.me/theorems/6034113d-4d15-4946-8635-46a647505d31
-- title:
--   The Lean 4 theorem `mem_finiteModes` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mem_finiteModes` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesEsa.lean

-- Generated from ChapterNavierStokesEsa.lean — theorem BookProof.NavierStokesFlow.mem_finiteModes
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow








open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

















variable {ι : Type*}









open BookProof.ChapterContinuityUnitaryInfinite

theorem BookProof.NavierStokesFlow.mem_finiteModes {f : L2Z} :
    f ∈ finiteModes ↔ (Function.support ((f : ℤ → ℂ))).Finite := by sorry
