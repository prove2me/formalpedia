-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY2_uField2_pderiv_y_twice
-- name    : BookProof.NavierStokesGaugeY2.uField2_pderiv_y_twice
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:25:36.357381+00:00
-- url     : https://prove2.me/theorems/c8778262-7a91-4472-b55d-7e1f434178db
-- title:
--   `BookProof.NavierStokesGaugeY2.uField2_pderiv_y_twice` (i j : Fin 3) : pderiv (NSVar.y j) (pderiv (NSVar.y j) (uField2 i)) = X (NSVar.uL i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY2`.
--
--   `BookProof.NavierStokesGaugeY2.uField2_pderiv_y_twice` (i j : Fin 3) : pderiv (NSVar.y j) (pderiv (NSVar.y j) (uField2 i)) = X (NSVar.uL i)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY2.uField2_pderiv_y_twice`.

-- Generated from ChapterNavierStokesGaugeY2.lean — theorem BookProof.NavierStokesGaugeY2.uField2_pderiv_y_twice
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY2



open MvPolynomial BookProof.NavierStokesGaugeY

theorem BookProof.NavierStokesGaugeY2.uField2_pderiv_y_twice (i j : Fin 3) :
    pderiv (NSVar.y j) (pderiv (NSVar.y j) (uField2 i)) = X (NSVar.uL i) := by sorry
