-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY2_uField2_pderiv_y
-- name    : BookProof.NavierStokesGaugeY2.uField2_pderiv_y
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:25:25.029147+00:00
-- url     : https://prove2.me/theorems/85bad757-1ead-4012-8436-e1febe710cfa
-- title:
--   `BookProof.NavierStokesGaugeY2.uField2_pderiv_y` (i j : Fin 3) : pderiv (NSVar.y j) (uField2 i) = uDField i j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY2`.
--
--   `BookProof.NavierStokesGaugeY2.uField2_pderiv_y` (i j : Fin 3) : pderiv (NSVar.y j) (uField2 i) = uDField i j
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY2.uField2_pderiv_y`.

-- Generated from ChapterNavierStokesGaugeY2.lean — theorem BookProof.NavierStokesGaugeY2.uField2_pderiv_y
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY2



open MvPolynomial BookProof.NavierStokesGaugeY

theorem BookProof.NavierStokesGaugeY2.uField2_pderiv_y (i j : Fin 3) :
    pderiv (NSVar.y j) (uField2 i) = uDField i j := by sorry
