-- Prove2me | Theorems.Thm_BookProof_NavierStokesEulerian_dirDeriv_dirDeriv
-- name    : BookProof.NavierStokesEulerian.dirDeriv_dirDeriv
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:38:50.512989+00:00
-- url     : https://prove2.me/theorems/c015ebe9-5bdb-44d2-9f5b-131a6c19baa4
-- title:
--   `BookProof.NavierStokesEulerian.dirDeriv_dirDeriv` (f : (Fin 3 → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (j k : Fin 3) (x : Fin 3 → ℝ) : dirDeriv (dirDeriv f j) k x = fderiv ℝ (fderiv ℝ f) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesEulerian`.
--
--   `BookProof.NavierStokesEulerian.dirDeriv_dirDeriv` (f : (Fin 3 → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (j k : Fin 3) (x : Fin 3 → ℝ) : dirDeriv (dirDeriv f j) k x = fderiv ℝ (fderiv ℝ f) x (evec k) (evec j)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesEulerian.dirDeriv_dirDeriv`.

-- Generated from ChapterNavierStokesEulerian.lean — theorem BookProof.NavierStokesEulerian.dirDeriv_dirDeriv
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
open BookProof.NavierStokesEulerian



open BookProof.NavierStokesFlow Matrix

theorem BookProof.NavierStokesEulerian.dirDeriv_dirDeriv (f : (Fin 3 → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (j k : Fin 3)
    (x : Fin 3 → ℝ) :
    dirDeriv (dirDeriv f j) k x = fderiv ℝ (fderiv ℝ f) x (evec k) (evec j) := by sorry
