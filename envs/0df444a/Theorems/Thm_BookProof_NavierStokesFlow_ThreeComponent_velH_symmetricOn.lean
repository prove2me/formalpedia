-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_velH_symmetricOn
-- name    : BookProof.NavierStokesFlow.ThreeComponent.velH_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:08:29.100145+00:00
-- url     : https://prove2.me/theorems/ad506f20-b52c-44e0-b19d-aca04217581f
-- title:
--   The Lean 4 theorem `velH_symmetricOn` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `velH_symmetricOn` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.velH_symmetricOn
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.velH_symmetricOn : SymmetricOn (maxDom (velSym (velMu A c))) (velH A c) := by sorry
