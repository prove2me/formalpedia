-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_velH_coord_diag_tower
-- name    : BookProof.NavierStokesFlow.ThreeComponent.velH_coord_diag_tower
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:18:36.451985+00:00
-- url     : https://prove2.me/theorems/2e798e3e-5169-4681-bbd5-e76bdebeb3db
-- title:
--   The Lean 4 theorem `velH_coord_diag_tower` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `velH_coord_diag_tower` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.velH_coord_diag_tower
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

set_option maxHeartbeats 1000000 in
-- the twenty-four members of the family are expanded and evaluated one by one

theorem BookProof.NavierStokesFlow.ThreeComponent.velH_coord_diag_tower (n : ℕ) :
    ((velH A c (velState A c ![n + 1, 0, 0]) : L2I Vel) : Vel → ℂ) ![n + 3, 0, 0]
      = Complex.I * ((A 0 0 / 2 * Real.sqrt (((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2)) : ℝ) : ℂ) := by sorry
