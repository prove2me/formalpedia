-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_genX_uField
-- name    : BookProof.NavierStokesGaugeY.genX_uField
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:24:20.351956+00:00
-- url     : https://prove2.me/theorems/d270c988-7eb0-45ba-9972-6ee869f5db51
-- title:
--   `BookProof.NavierStokesGaugeY.genX_uField` (i j : Fin 3) : genX j (uField i) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.genX_uField` (i j : Fin 3) : genX j (uField i) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.genX_uField`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.genX_uField
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.genX_uField (i j : Fin 3) : genX j (uField i) = 0 := by sorry
