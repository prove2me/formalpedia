-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY2_genY_genY2_bracket_X_u
-- name    : BookProof.NavierStokesGaugeY2.genY_genY2_bracket_X_u
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:04:27.539878+00:00
-- url     : https://prove2.me/theorems/9a25f571-0141-47dc-a94a-aff6700ca375
-- title:
--   `BookProof.NavierStokesGaugeY2.genY_genY2_bracket_X_u` (i j : Fin 3) : ⁅genY j, genY2 j⁆ (X (NSVar.u i)) = -X (NSVar.uL i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY2`.
--
--   `BookProof.NavierStokesGaugeY2.genY_genY2_bracket_X_u` (i j : Fin 3) : ⁅genY j, genY2 j⁆ (X (NSVar.u i)) = -X (NSVar.uL i)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY2.genY_genY2_bracket_X_u`.

-- Generated from ChapterNavierStokesGaugeY2.lean — theorem BookProof.NavierStokesGaugeY2.genY_genY2_bracket_X_u
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY2



open MvPolynomial BookProof.NavierStokesGaugeY

theorem BookProof.NavierStokesGaugeY2.genY_genY2_bracket_X_u (i j : Fin 3) :
    ⁅genY j, genY2 j⁆ (X (NSVar.u i)) = -X (NSVar.uL i) := by sorry
