-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_diagHop_shift
-- name    : BookProof.NavierStokesFlow.ThreeComponent.diagHop_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:04:28.934591+00:00
-- url     : https://prove2.me/theorems/641528c8-22f8-469f-8f66-20d9a1f72ad7
-- title:
--   The Lean 4 theorem `diagHop_shift` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `diagHop_shift` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.diagHop_shift
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.diagHop_shift (i : Fin 3) : (diagHop A c i).shift = shDiag i := by sorry
