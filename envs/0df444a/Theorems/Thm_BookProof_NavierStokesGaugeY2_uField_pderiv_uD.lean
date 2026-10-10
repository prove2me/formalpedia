-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY2_uField_pderiv_uD
-- name    : BookProof.NavierStokesGaugeY2.uField_pderiv_uD
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:27:23.170486+00:00
-- url     : https://prove2.me/theorems/860f2530-a66f-4f12-a8d5-c6d457726f94
-- title:
--   `BookProof.NavierStokesGaugeY2.uField_pderiv_uD` (m k i : Fin 3) : pderiv (NSVar.uD m k) (uField i) = if m = i then X (NSVar.y k) else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY2`.
--
--   `BookProof.NavierStokesGaugeY2.uField_pderiv_uD` (m k i : Fin 3) : pderiv (NSVar.uD m k) (uField i) = if m = i then X (NSVar.y k) else 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY2.uField_pderiv_uD`.

-- Generated from ChapterNavierStokesGaugeY2.lean — theorem BookProof.NavierStokesGaugeY2.uField_pderiv_uD
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY2



open MvPolynomial BookProof.NavierStokesGaugeY

theorem BookProof.NavierStokesGaugeY2.uField_pderiv_uD (m k i : Fin 3) :
    pderiv (NSVar.uD m k) (uField i) = if m = i then X (NSVar.y k) else 0 := by sorry
