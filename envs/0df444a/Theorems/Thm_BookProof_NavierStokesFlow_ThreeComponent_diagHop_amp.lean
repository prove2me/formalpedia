-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_diagHop_amp
-- name    : BookProof.NavierStokesFlow.ThreeComponent.diagHop_amp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:04:22.565638+00:00
-- url     : https://prove2.me/theorems/41a7d83c-6672-41be-9d46-ae17159b3150
-- title:
--   The Lean 4 theorem `diagHop_amp` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `diagHop_amp` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.diagHop_amp
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.diagHop_amp (i : Fin 3) : (diagHop A c i).amp = ampDiag A i := by sorry
