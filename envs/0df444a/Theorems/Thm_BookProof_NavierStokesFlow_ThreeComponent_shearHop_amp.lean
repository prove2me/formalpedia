-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_shearHop_amp
-- name    : BookProof.NavierStokesFlow.ThreeComponent.shearHop_amp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:05:07.589539+00:00
-- url     : https://prove2.me/theorems/d0b92e7c-c883-4251-bf00-0750f81419cc
-- title:
--   The Lean 4 theorem `shearHop_amp` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `shearHop_amp` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.shearHop_amp
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.shearHop_amp (i : Fin 3) : (shearHop A c i).amp = ampShear c i := by sorry
