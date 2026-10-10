-- Prove2me | Theorems.Thm_BookProof_NavierStokesEulerian_derivativeField_consistency
-- name    : BookProof.NavierStokesEulerian.derivativeField_consistency
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:40:31.957815+00:00
-- url     : https://prove2.me/theorems/eb3d7f0a-66df-4061-96a7-c074d6f9e9d9
-- title:
--   `BookProof.NavierStokesEulerian.derivativeField_consistency` (u : (Fin 3 → ℝ) → Fin 3 → ℝ) (hu : ∀ i, ContDiff ℝ 2 (fun y => u y i)) (i j k : Fin 3) (x : Fin 3 → ℝ) : dirDeriv (dir
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesEulerian`.
--
--   `BookProof.NavierStokesEulerian.derivativeField_consistency` (u : (Fin 3 → ℝ) → Fin 3 → ℝ) (hu : ∀ i, ContDiff ℝ 2 (fun y => u y i)) (i j k : Fin 3) (x : Fin 3 → ℝ) : dirDeriv (dirDeriv (fun y => u y i) j) k x = dirDeriv (dirDeriv (fun y => u y i) k) j x
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesEulerian.derivativeField_consistency`.

-- Generated from ChapterNavierStokesEulerian.lean — theorem BookProof.NavierStokesEulerian.derivativeField_consistency
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
open BookProof.NavierStokesEulerian



open BookProof.NavierStokesFlow Matrix

theorem BookProof.NavierStokesEulerian.derivativeField_consistency (u : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (hu : ∀ i, ContDiff ℝ 2 (fun y => u y i)) (i j k : Fin 3) (x : Fin 3 → ℝ) :
    dirDeriv (dirDeriv (fun y => u y i) j) k x
      = dirDeriv (dirDeriv (fun y => u y i) k) j x := by sorry
