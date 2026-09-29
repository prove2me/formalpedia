-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_rotHop_amp
-- name    : BookProof.NavierStokesFlow.ThreeComponent.rotHop_amp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:04:54.686294+00:00
-- url     : https://prove2.me/theorems/8d1d2a35-8fe3-4ef9-8656-e7986dd1e02e
-- title:
--   The Lean 4 theorem `rotHop_amp` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `rotHop_amp` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.rotHop_amp
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.rotHop_amp (i k : Fin 3) : (rotHop A c i k).amp = ampRot A i k := by sorry
