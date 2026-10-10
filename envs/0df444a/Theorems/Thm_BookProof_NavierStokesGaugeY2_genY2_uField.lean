-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY2_genY2_uField
-- name    : BookProof.NavierStokesGaugeY2.genY2_uField
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:44:18.477974+00:00
-- url     : https://prove2.me/theorems/2e53baa5-0b1f-4455-9699-2e0995ff5c7f
-- title:
--   `BookProof.NavierStokesGaugeY2.genY2_uField` (i j : Fin 3) : genY2 j (uField i) = -(X (NSVar.uL i) * X (NSVar.y j))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY2`.
--
--   `BookProof.NavierStokesGaugeY2.genY2_uField` (i j : Fin 3) : genY2 j (uField i) = -(X (NSVar.uL i) * X (NSVar.y j))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY2.genY2_uField`.

-- Generated from ChapterNavierStokesGaugeY2.lean — theorem BookProof.NavierStokesGaugeY2.genY2_uField
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY2



open MvPolynomial BookProof.NavierStokesGaugeY

theorem BookProof.NavierStokesGaugeY2.genY2_uField (i j : Fin 3) :
    genY2 j (uField i) = -(X (NSVar.uL i) * X (NSVar.y j)) := by sorry
