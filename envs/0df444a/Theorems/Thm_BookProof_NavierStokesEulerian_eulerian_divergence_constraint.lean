-- Prove2me | Theorems.Thm_BookProof_NavierStokesEulerian_eulerian_divergence_constraint
-- name    : BookProof.NavierStokesEulerian.eulerian_divergence_constraint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:42:02.103505+00:00
-- url     : https://prove2.me/theorems/2d0513b0-3551-480c-8ddd-678840f32239
-- title:
--   `BookProof.NavierStokesEulerian.eulerian_divergence_constraint` (u : (Fin 3 → ℝ) → Fin 3 → ℝ) (x : Fin 3 → ℝ) (h : dirDeriv (fun y => u y 2) 2 x = -(dirDeriv (fun y => u y 0) 0 x +
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesEulerian`.
--
--   `BookProof.NavierStokesEulerian.eulerian_divergence_constraint` (u : (Fin 3 → ℝ) → Fin 3 → ℝ) (x : Fin 3 → ℝ) (h : dirDeriv (fun y => u y 2) 2 x = -(dirDeriv (fun y => u y 0) 0 x + dirDeriv (fun y => u y 1) 1 x)) : ∑ j : Fin 3, dirDeriv (fun y => u y j) j x = 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesEulerian.eulerian_divergence_constraint`.

-- Generated from ChapterNavierStokesEulerian.lean — theorem BookProof.NavierStokesEulerian.eulerian_divergence_constraint
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
open BookProof.NavierStokesEulerian



open BookProof.NavierStokesFlow Matrix

theorem BookProof.NavierStokesEulerian.eulerian_divergence_constraint (u : (Fin 3 → ℝ) → Fin 3 → ℝ) (x : Fin 3 → ℝ)
    (h : dirDeriv (fun y => u y 2) 2 x
      = -(dirDeriv (fun y => u y 0) 0 x + dirDeriv (fun y => u y 1) 1 x)) :
    ∑ j : Fin 3, dirDeriv (fun y => u y j) j x = 0 := by sorry
