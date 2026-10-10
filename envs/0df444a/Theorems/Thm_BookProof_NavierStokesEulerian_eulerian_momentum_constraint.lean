-- Prove2me | Theorems.Thm_BookProof_NavierStokesEulerian_eulerian_momentum_constraint
-- name    : BookProof.NavierStokesEulerian.eulerian_momentum_constraint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:39:00.028864+00:00
-- url     : https://prove2.me/theorems/d172211f-a1f6-45ca-a8e9-cf538f2bff89
-- title:
--   `BookProof.NavierStokesEulerian.eulerian_momentum_constraint` (j k : Fin 3) (p : MvPolynomial (Fin 3) ℂ) : (MvPolynomial.pderiv k) (MvPolynomial.X j * p) - MvPolynomial.X j * (MvPo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesEulerian`.
--
--   `BookProof.NavierStokesEulerian.eulerian_momentum_constraint` (j k : Fin 3) (p : MvPolynomial (Fin 3) ℂ) : (MvPolynomial.pderiv k) (MvPolynomial.X j * p) - MvPolynomial.X j * (MvPolynomial.pderiv k) p = (if k = j then p else 0)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesEulerian.eulerian_momentum_constraint`.

-- Generated from ChapterNavierStokesEulerian.lean — theorem BookProof.NavierStokesEulerian.eulerian_momentum_constraint
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesEulerian
open BookProof.NavierStokesEulerian



open BookProof.NavierStokesFlow Matrix

theorem BookProof.NavierStokesEulerian.eulerian_momentum_constraint (j k : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    (MvPolynomial.pderiv k) (MvPolynomial.X j * p)
      - MvPolynomial.X j * (MvPolynomial.pderiv k) p = (if k = j then p else 0) := by sorry
