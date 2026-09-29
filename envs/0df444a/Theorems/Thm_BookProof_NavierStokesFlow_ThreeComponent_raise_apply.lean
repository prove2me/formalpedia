-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_raise_apply
-- name    : BookProof.NavierStokesFlow.ThreeComponent.raise_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:04:44.524073+00:00
-- url     : https://prove2.me/theorems/019d4dda-6bbc-46b9-9ee6-31c661c41f23
-- title:
--   The Lean 4 theorem `raise_apply` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `raise_apply` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.raise_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.raise_apply (i : Fin 3) (β : Vel) (j : Fin 3) :
    raise i β j = β j + (if j = i then 1 else 0) := by sorry
