-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_pderiv_u_mul_uD
-- name    : BookProof.NavierStokesGaugeY.pderiv_u_mul_uD
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:24:32.831982+00:00
-- url     : https://prove2.me/theorems/db660c7b-94ae-4d4e-8a3c-119c31aceda9
-- title:
--   `BookProof.NavierStokesGaugeY.pderiv_u_mul_uD` (m i j : Fin 3) (q : NSAlg) : pderiv (NSVar.u m) (X (NSVar.uD i j) * q) = X (NSVar.uD i j) * pderiv (NSVar.u m) q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.pderiv_u_mul_uD` (m i j : Fin 3) (q : NSAlg) : pderiv (NSVar.u m) (X (NSVar.uD i j) * q) = X (NSVar.uD i j) * pderiv (NSVar.u m) q
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.pderiv_u_mul_uD`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.pderiv_u_mul_uD
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.pderiv_u_mul_uD (m i j : Fin 3) (q : NSAlg) :
    pderiv (NSVar.u m) (X (NSVar.uD i j) * q) = X (NSVar.uD i j) * pderiv (NSVar.u m) q := by sorry
