-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_shDiag_apply
-- name    : BookProof.NavierStokesFlow.ThreeComponent.shDiag_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:05:09.51822+00:00
-- url     : https://prove2.me/theorems/6d633edc-59d0-4bb1-a2d8-4d88505c4bdc
-- title:
--   The Lean 4 theorem `shDiag_apply` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `shDiag_apply` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.shDiag_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.shDiag_apply (i : Fin 3) (β : Vel) (j : Fin 3) :
    shDiag i β j = β j + (if j = i then 2 else 0) := by sorry
