-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_single_mem_finiteModes
-- name    : BookProof.NavierStokesFlow.single_mem_finiteModes
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:12:26.227654+00:00
-- url     : https://prove2.me/theorems/ef9c08b5-7524-4970-8ccc-ba7a896b3608
-- title:
--   The Lean 4 theorem `single_mem_finiteModes` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `single_mem_finiteModes` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesEsa.lean

-- Generated from ChapterNavierStokesEsa.lean — theorem BookProof.NavierStokesFlow.single_mem_finiteModes
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow








open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

















variable {ι : Type*}









open BookProof.ChapterContinuityUnitaryInfinite

theorem BookProof.NavierStokesFlow.single_mem_finiteModes (k : ℤ) (c : ℂ) : lp.single 2 k c ∈ finiteModes := by sorry
