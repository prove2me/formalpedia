-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_rotHop_shift
-- name    : BookProof.NavierStokesFlow.ThreeComponent.rotHop_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:04:55.640976+00:00
-- url     : https://prove2.me/theorems/2f75bf4e-4265-4c7e-b646-b80298cd96f7
-- title:
--   The Lean 4 theorem `rotHop_shift` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `rotHop_shift` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.rotHop_shift
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.rotHop_shift (i k : Fin 3) : (rotHop A c i k).shift = shRot i k := by sorry
