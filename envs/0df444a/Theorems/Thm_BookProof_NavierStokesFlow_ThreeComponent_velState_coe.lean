-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_velState_coe
-- name    : BookProof.NavierStokesFlow.ThreeComponent.velState_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:08:34.003751+00:00
-- url     : https://prove2.me/theorems/4f660e4e-c5d4-4454-b307-2bbedbd42070
-- title:
--   The Lean 4 theorem `velState_coe` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `velState_coe` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.velState_coe
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.velState_coe (β α : Vel) :
    ((velState A c β : L2I Vel) : Vel → ℂ) α = if α = β then 1 else 0 := by sorry
