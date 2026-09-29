-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_velH_coord_pair
-- name    : BookProof.NavierStokesFlow.ThreeComponent.velH_coord_pair
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:18:45.23402+00:00
-- url     : https://prove2.me/theorems/9484ad6a-5c9c-4430-bf4d-ac9facaa66b8
-- title:
--   The Lean 4 theorem `velH_coord_pair` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `velH_coord_pair` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.velH_coord_pair
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

set_option maxHeartbeats 1000000 in
-- the twenty-four members of the family are expanded and evaluated one by one

theorem BookProof.NavierStokesFlow.ThreeComponent.velH_coord_pair :
    ((velH A c (velState A c ![0, 0, 0]) : L2I Vel) : Vel → ℂ) ![1, 1, 0]
      = Complex.I * (((A 0 1 + A 1 0) / 2 : ℝ) : ℂ) := by sorry
