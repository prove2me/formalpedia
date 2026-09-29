-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_shearHop_shift
-- name    : BookProof.NavierStokesFlow.ThreeComponent.shearHop_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:05:22.58879+00:00
-- url     : https://prove2.me/theorems/d84bcbfa-0af5-4b7e-be27-461e3c8d637e
-- title:
--   The Lean 4 theorem `shearHop_shift` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `shearHop_shift` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.shearHop_shift
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.shearHop_shift (i : Fin 3) : (shearHop A c i).shift = shShear i := by sorry
