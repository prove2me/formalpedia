-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_setYZero_uField
-- name    : BookProof.NavierStokesGaugeY.setYZero_uField
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:21:38.237219+00:00
-- url     : https://prove2.me/theorems/91070dcf-5828-4b1d-8d33-ac6c25b545b4
-- title:
--   `BookProof.NavierStokesGaugeY.setYZero_uField` (i : Fin 3) : setYZero (uField i) = X (NSVar.u i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.setYZero_uField` (i : Fin 3) : setYZero (uField i) = X (NSVar.u i)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.setYZero_uField`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.setYZero_uField
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.setYZero_uField (i : Fin 3) : setYZero (uField i) = X (NSVar.u i) := by sorry
