-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_shShear_apply
-- name    : BookProof.NavierStokesFlow.ThreeComponent.shShear_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:11:46.027875+00:00
-- url     : https://prove2.me/theorems/57cd8ce6-daeb-4b53-b059-3183310cac1c
-- title:
--   The Lean 4 theorem `shShear_apply` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `shShear_apply` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.shShear_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.shShear_apply (i : Fin 3) (β : Vel) (j : Fin 3) :
    shShear i β j = β j + (if j = i then 1 else 0) := by sorry
