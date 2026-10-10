-- Prove2me | Theorems.Thm_BookProof_NavierStokesEulerian_dirDeriv_eq
-- name    : BookProof.NavierStokesEulerian.dirDeriv_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:39:07.782985+00:00
-- url     : https://prove2.me/theorems/9e2ccdb7-6e8d-4477-a9c6-666b2a59b5da
-- title:
--   `BookProof.NavierStokesEulerian.dirDeriv_eq` {f : (Fin 3 → ℝ) → ℝ} {L : (Fin 3 → ℝ) →L[ℝ] ℝ} {x : Fin 3 → ℝ} (hf : HasFDerivAt f L x) (j : Fin 3) : dirDeriv f j x = L (evec j)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesEulerian`.
--
--   `BookProof.NavierStokesEulerian.dirDeriv_eq` {f : (Fin 3 → ℝ) → ℝ} {L : (Fin 3 → ℝ) →L[ℝ] ℝ} {x : Fin 3 → ℝ} (hf : HasFDerivAt f L x) (j : Fin 3) : dirDeriv f j x = L (evec j)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesEulerian.dirDeriv_eq`.

-- Generated from ChapterNavierStokesEulerian.lean — theorem BookProof.NavierStokesEulerian.dirDeriv_eq
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
open BookProof.NavierStokesEulerian



open BookProof.NavierStokesFlow Matrix

theorem BookProof.NavierStokesEulerian.dirDeriv_eq {f : (Fin 3 → ℝ) → ℝ} {L : (Fin 3 → ℝ) →L[ℝ] ℝ} {x : Fin 3 → ℝ}
    (hf : HasFDerivAt f L x) (j : Fin 3) : dirDeriv f j x = L (evec j) := by sorry
