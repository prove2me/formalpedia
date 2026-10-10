-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_pderiv_y_mul_uD
-- name    : BookProof.NavierStokesGaugeY.pderiv_y_mul_uD
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:24:17.355107+00:00
-- url     : https://prove2.me/theorems/8a296b8b-6558-4aae-81f3-db43bf9d3ffe
-- title:
--   `BookProof.NavierStokesGaugeY.pderiv_y_mul_uD` (m i j : Fin 3) (q : NSAlg) : pderiv (NSVar.y m) (X (NSVar.uD i j) * q) = X (NSVar.uD i j) * pderiv (NSVar.y m) q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.pderiv_y_mul_uD` (m i j : Fin 3) (q : NSAlg) : pderiv (NSVar.y m) (X (NSVar.uD i j) * q) = X (NSVar.uD i j) * pderiv (NSVar.y m) q
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.pderiv_y_mul_uD`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.pderiv_y_mul_uD
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.pderiv_y_mul_uD (m i j : Fin 3) (q : NSAlg) :
    pderiv (NSVar.y m) (X (NSVar.uD i j) * q) = X (NSVar.uD i j) * pderiv (NSVar.y m) q := by sorry
