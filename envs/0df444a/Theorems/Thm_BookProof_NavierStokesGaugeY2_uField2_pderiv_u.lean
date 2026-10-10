-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY2_uField2_pderiv_u
-- name    : BookProof.NavierStokesGaugeY2.uField2_pderiv_u
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:25:44.628885+00:00
-- url     : https://prove2.me/theorems/54f37e10-d1ef-44ff-ae26-4dc3d3301b76
-- title:
--   `BookProof.NavierStokesGaugeY2.uField2_pderiv_u` (m i : Fin 3) : pderiv (NSVar.u m) (uField2 i) = if m = i then 1 else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY2`.
--
--   `BookProof.NavierStokesGaugeY2.uField2_pderiv_u` (m i : Fin 3) : pderiv (NSVar.u m) (uField2 i) = if m = i then 1 else 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY2.uField2_pderiv_u`.

-- Generated from ChapterNavierStokesGaugeY2.lean — theorem BookProof.NavierStokesGaugeY2.uField2_pderiv_u
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY2



open MvPolynomial BookProof.NavierStokesGaugeY

theorem BookProof.NavierStokesGaugeY2.uField2_pderiv_u (m i : Fin 3) :
    pderiv (NSVar.u m) (uField2 i) = if m = i then 1 else 0 := by sorry
