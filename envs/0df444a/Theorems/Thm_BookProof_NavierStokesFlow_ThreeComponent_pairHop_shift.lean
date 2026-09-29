-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_pairHop_shift
-- name    : BookProof.NavierStokesFlow.ThreeComponent.pairHop_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:04:58.385784+00:00
-- url     : https://prove2.me/theorems/3703941c-f435-4294-805e-f4a71b4aef50
-- title:
--   The Lean 4 theorem `pairHop_shift` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pairHop_shift` in the `ChapterNavierStokesThreeComponent` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesThreeComponent.lean

-- Generated from ChapterNavierStokesThreeComponent.lean — theorem BookProof.NavierStokesFlow.ThreeComponent.pairHop_shift
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open scoped ENNReal
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.ThreeComponent.pairHop_shift (i k : Fin 3) : (pairHop A c i k).shift = shPair i k := by sorry
