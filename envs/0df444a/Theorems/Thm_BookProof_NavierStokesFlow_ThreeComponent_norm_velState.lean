-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_norm_velState
-- name    : BookProof.NavierStokesFlow.ThreeComponent.norm_velState
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:04:43.616962+00:00
-- url     : https://prove2.me/theorems/b089e001-3aad-4806-8920-6c6611c924fb
-- title:
--   The Lean 4 theorem `norm_velState` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_velState` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.norm_velState
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.norm_velState (β : Vel) : ‖(velState A c β : L2I Vel)‖ = 1 := by sorry
