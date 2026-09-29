-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_velH_coord_rot
-- name    : BookProof.NavierStokesFlow.ThreeComponent.velH_coord_rot
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:20:27.478932+00:00
-- url     : https://prove2.me/theorems/27d5f008-6b16-484c-83a8-4519849c3f9f
-- title:
--   The Lean 4 theorem `velH_coord_rot` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `velH_coord_rot` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.velH_coord_rot
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

set_option maxHeartbeats 1000000 in
-- the twenty-four members of the family are expanded and evaluated one by one

theorem BookProof.NavierStokesFlow.ThreeComponent.velH_coord_rot :
    ((velH A c (velState A c ![0, 1, 0]) : L2I Vel) : Vel → ℂ) ![1, 0, 0]
      = Complex.I * (((A 0 1 - A 1 0) / 2 : ℝ) : ℂ) := by sorry
