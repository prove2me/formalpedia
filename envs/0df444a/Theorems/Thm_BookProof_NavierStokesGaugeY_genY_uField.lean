-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_genY_uField
-- name    : BookProof.NavierStokesGaugeY.genY_uField
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:42:42.310037+00:00
-- url     : https://prove2.me/theorems/871b547a-50fa-40b4-8aad-aeecae268341
-- title:
--   `BookProof.NavierStokesGaugeY.genY_uField` (i j : Fin 3) : genY j (uField i) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.genY_uField` (i j : Fin 3) : genY j (uField i) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.genY_uField`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.genY_uField
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.genY_uField (i j : Fin 3) : genY j (uField i) = 0 := by sorry
