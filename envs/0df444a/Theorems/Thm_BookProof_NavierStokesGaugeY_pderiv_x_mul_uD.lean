-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_pderiv_x_mul_uD
-- name    : BookProof.NavierStokesGaugeY.pderiv_x_mul_uD
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:23:52.811657+00:00
-- url     : https://prove2.me/theorems/91b453e8-2b80-46ab-b753-5dae28b9d7b5
-- title:
--   `BookProof.NavierStokesGaugeY.pderiv_x_mul_uD` (m i j : Fin 3) (q : NSAlg) : pderiv (NSVar.x m) (X (NSVar.uD i j) * q) = X (NSVar.uD i j) * pderiv (NSVar.x m) q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.pderiv_x_mul_uD` (m i j : Fin 3) (q : NSAlg) : pderiv (NSVar.x m) (X (NSVar.uD i j) * q) = X (NSVar.uD i j) * pderiv (NSVar.x m) q
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.pderiv_x_mul_uD`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.pderiv_x_mul_uD
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.pderiv_x_mul_uD (m i j : Fin 3) (q : NSAlg) :
    pderiv (NSVar.x m) (X (NSVar.uD i j) * q) = X (NSVar.uD i j) * pderiv (NSVar.x m) q := by sorry
