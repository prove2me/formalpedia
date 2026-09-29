-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_velH_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.ThreeComponent.velH_essentiallySelfAdjointOn_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:25:27.960172+00:00
-- url     : https://prove2.me/theorems/81aa2390-3751-47d9-ab4b-40ec47d3ba74
-- title:
--   The Lean 4 theorem `velH_essentiallySelfAdjointOn_core` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `velH_essentiallySelfAdjointOn_core` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.velH_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.velH_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (lpFiniteModes Vel)
      ((velH A c).comp (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))))) := by sorry
