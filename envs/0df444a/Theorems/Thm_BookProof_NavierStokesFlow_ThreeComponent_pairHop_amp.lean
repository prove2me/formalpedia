-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_pairHop_amp
-- name    : BookProof.NavierStokesFlow.ThreeComponent.pairHop_amp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:04:50.526206+00:00
-- url     : https://prove2.me/theorems/37da8586-7ea7-4fc4-b542-2fdab71a6655
-- title:
--   The Lean 4 theorem `pairHop_amp` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pairHop_amp` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.pairHop_amp
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.pairHop_amp (i k : Fin 3) : (pairHop A c i k).amp = ampPair A i k := by sorry
