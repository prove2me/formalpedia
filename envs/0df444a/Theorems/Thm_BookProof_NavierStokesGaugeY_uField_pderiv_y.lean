-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_uField_pderiv_y
-- name    : BookProof.NavierStokesGaugeY.uField_pderiv_y
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:24:08.31231+00:00
-- url     : https://prove2.me/theorems/69e6cbf2-2e19-4a0f-8e4a-46ce4106e255
-- title:
--   `BookProof.NavierStokesGaugeY.uField_pderiv_y` (i j : Fin 3) : pderiv (NSVar.y j) (uField i) = X (NSVar.uD i j)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.uField_pderiv_y` (i j : Fin 3) : pderiv (NSVar.y j) (uField i) = X (NSVar.uD i j)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.uField_pderiv_y`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.uField_pderiv_y
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.uField_pderiv_y (i j : Fin 3) :
    pderiv (NSVar.y j) (uField i) = X (NSVar.uD i j) := by sorry
