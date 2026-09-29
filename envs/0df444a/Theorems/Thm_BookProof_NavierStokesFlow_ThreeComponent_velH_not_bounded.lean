-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_velH_not_bounded
-- name    : BookProof.NavierStokesFlow.ThreeComponent.velH_not_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:53:13.661016+00:00
-- url     : https://prove2.me/theorems/a7de2e41-52f7-400f-abb5-fa72e3891c2b
-- title:
--   The Lean 4 theorem `velH_not_bounded` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `velH_not_bounded` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.velH_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.velH_not_bounded (hA : A 0 0 ≠ 0) (C : ℝ) :
    ∃ β : Vel, ‖(velState A c β : L2I Vel)‖ = 1
      ∧ C < ‖(velH A c (velState A c β) : L2I Vel)‖ := by sorry
