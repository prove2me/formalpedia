-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_shPair_apply
-- name    : BookProof.NavierStokesFlow.ThreeComponent.shPair_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:11:46.227495+00:00
-- url     : https://prove2.me/theorems/d94e8a83-89de-4426-b5f6-08970a2fce39
-- title:
--   The Lean 4 theorem `shPair_apply` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `shPair_apply` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.shPair_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.shPair_apply (i k : Fin 3) (β : Vel) (j : Fin 3) :
    shPair i k β j = β j + (if j = k then 1 else 0) + (if j = i then 1 else 0) := by sorry
