-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY2_genY_uField2
-- name    : BookProof.NavierStokesGaugeY2.genY_uField2
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:46:45.535959+00:00
-- url     : https://prove2.me/theorems/055673bf-7e82-4af2-ab10-90b20c82cd14
-- title:
--   `BookProof.NavierStokesGaugeY2.genY_uField2` (i j : Fin 3) : genY j (uField2 i) = X (NSVar.uL i) * X (NSVar.y j)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY2`.
--
--   `BookProof.NavierStokesGaugeY2.genY_uField2` (i j : Fin 3) : genY j (uField2 i) = X (NSVar.uL i) * X (NSVar.y j)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY2.genY_uField2`.

-- Generated from ChapterNavierStokesGaugeY2.lean — theorem BookProof.NavierStokesGaugeY2.genY_uField2
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY2



open MvPolynomial BookProof.NavierStokesGaugeY

theorem BookProof.NavierStokesGaugeY2.genY_uField2 (i j : Fin 3) :
    genY j (uField2 i) = X (NSVar.uL i) * X (NSVar.y j) := by sorry
