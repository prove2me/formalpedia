-- Prove2me | Theorems.Thm_BookProof_NavierStokesEulerian_eulerian_momentum_dual
-- name    : BookProof.NavierStokesEulerian.eulerian_momentum_dual
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:40:33.318979+00:00
-- url     : https://prove2.me/theorems/0c20baab-5cdc-4403-a756-0c377422c780
-- title:
--   `BookProof.NavierStokesEulerian.eulerian_momentum_dual` (i j k l : Fin 3) : (MvPolynomial.pderiv (i, j)) (MvPolynomial.X (k, l) : MvPolynomial (Fin 3 × Fin 3) ℂ) = if i = k ∧ j = l
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesEulerian`.
--
--   `BookProof.NavierStokesEulerian.eulerian_momentum_dual` (i j k l : Fin 3) : (MvPolynomial.pderiv (i, j)) (MvPolynomial.X (k, l) : MvPolynomial (Fin 3 × Fin 3) ℂ) = if i = k ∧ j = l then 1 else 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesEulerian.eulerian_momentum_dual`.

-- Generated from ChapterNavierStokesEulerian.lean — theorem BookProof.NavierStokesEulerian.eulerian_momentum_dual
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
open BookProof.NavierStokesEulerian



open BookProof.NavierStokesFlow Matrix

theorem BookProof.NavierStokesEulerian.eulerian_momentum_dual (i j k l : Fin 3) :
    (MvPolynomial.pderiv (i, j)) (MvPolynomial.X (k, l) : MvPolynomial (Fin 3 × Fin 3) ℂ)
      = if i = k ∧ j = l then 1 else 0 := by sorry
