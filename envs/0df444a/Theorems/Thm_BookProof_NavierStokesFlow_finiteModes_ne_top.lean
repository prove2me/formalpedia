-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_finiteModes_ne_top
-- name    : BookProof.NavierStokesFlow.finiteModes_ne_top
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:12:41.495731+00:00
-- url     : https://prove2.me/theorems/5bc2ae25-7582-4068-8a48-2a1b2eb9eb49
-- title:
--   The Lean 4 theorem `finiteModes_ne_top` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `finiteModes_ne_top` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesEsa.lean

-- Generated from ChapterNavierStokesEsa.lean — theorem BookProof.NavierStokesFlow.finiteModes_ne_top
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow








open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

















variable {ι : Type*}









open BookProof.ChapterContinuityUnitaryInfinite

theorem BookProof.NavierStokesFlow.finiteModes_ne_top : finiteModes ≠ (⊤ : Submodule ℂ L2Z) := by sorry
