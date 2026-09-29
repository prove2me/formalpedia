-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_hopList_eq
-- name    : BookProof.NavierStokesFlow.ThreeComponent.hopList_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:04:32.91158+00:00
-- url     : https://prove2.me/theorems/4f8fae1b-8856-4d92-9a18-d877630ba40f
-- title:
--   The Lean 4 theorem `hopList_eq` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hopList_eq` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.hopList_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.hopList_eq : hopList A c =
    [diagHop A c 0, shearHop A c 0,
      pairHop A c 0 0, rotHop A c 0 0, pairHop A c 0 1, rotHop A c 0 1,
      pairHop A c 0 2, rotHop A c 0 2,
     diagHop A c 1, shearHop A c 1,
      pairHop A c 1 0, rotHop A c 1 0, pairHop A c 1 1, rotHop A c 1 1,
      pairHop A c 1 2, rotHop A c 1 2,
     diagHop A c 2, shearHop A c 2,
      pairHop A c 2 0, rotHop A c 2 0, pairHop A c 2 1, rotHop A c 2 1,
      pairHop A c 2 2, rotHop A c 2 2] := by sorry
