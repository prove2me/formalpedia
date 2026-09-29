-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_velSym_of_total
-- name    : BookProof.NavierStokesFlow.ThreeComponent.velSym_of_total
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:08:28.508983+00:00
-- url     : https://prove2.me/theorems/20aaed7b-bbea-4ccd-89b4-b3bc6b3cf704
-- title:
--   The Lean 4 theorem `velSym_of_total` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `velSym_of_total` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.velSym_of_total
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.velSym_of_total {mu : ℝ} {β γ : Vel} {m : ℕ} (h : total γ = total β + m) :
    velSym mu γ = velSym mu β + 2 * mu * m := by sorry
