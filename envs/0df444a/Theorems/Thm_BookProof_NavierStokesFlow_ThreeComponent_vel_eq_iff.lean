-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_vel_eq_iff
-- name    : BookProof.NavierStokesFlow.ThreeComponent.vel_eq_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:08:38.892262+00:00
-- url     : https://prove2.me/theorems/6a28a391-7bd3-4f59-87d7-6a87cf3bcd8d
-- title:
--   The Lean 4 theorem `vel_eq_iff` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `vel_eq_iff` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.vel_eq_iff
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.vel_eq_iff (x y : Vel) : x = y ↔ x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 := by sorry
