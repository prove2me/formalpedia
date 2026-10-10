-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_uField_pderiv_x
-- name    : BookProof.NavierStokesGaugeY.uField_pderiv_x
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:24:31.158076+00:00
-- url     : https://prove2.me/theorems/2524989f-a93b-4557-8476-3be9feea35b6
-- title:
--   `BookProof.NavierStokesGaugeY.uField_pderiv_x` (i j : Fin 3) : pderiv (NSVar.x j) (uField i) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.uField_pderiv_x` (i j : Fin 3) : pderiv (NSVar.x j) (uField i) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.uField_pderiv_x`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.uField_pderiv_x
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.uField_pderiv_x (i j : Fin 3) : pderiv (NSVar.x j) (uField i) = 0 := by sorry
