-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY2_uField_pderiv_u
-- name    : BookProof.NavierStokesGaugeY2.uField_pderiv_u
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:26:06.123174+00:00
-- url     : https://prove2.me/theorems/f3812db9-4693-48c2-ba62-a8c2190c654f
-- title:
--   `BookProof.NavierStokesGaugeY2.uField_pderiv_u` (m i : Fin 3) : pderiv (NSVar.u m) (uField i) = if m = i then 1 else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY2`.
--
--   `BookProof.NavierStokesGaugeY2.uField_pderiv_u` (m i : Fin 3) : pderiv (NSVar.u m) (uField i) = if m = i then 1 else 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY2.uField_pderiv_u`.

-- Generated from ChapterNavierStokesGaugeY2.lean — theorem BookProof.NavierStokesGaugeY2.uField_pderiv_u
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY2



open MvPolynomial BookProof.NavierStokesGaugeY

theorem BookProof.NavierStokesGaugeY2.uField_pderiv_u (m i : Fin 3) :
    pderiv (NSVar.u m) (uField i) = if m = i then 1 else 0 := by sorry
