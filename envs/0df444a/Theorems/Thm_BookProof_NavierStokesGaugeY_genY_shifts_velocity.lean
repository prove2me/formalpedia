-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_genY_shifts_velocity
-- name    : BookProof.NavierStokesGaugeY.genY_shifts_velocity
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:42:38.002994+00:00
-- url     : https://prove2.me/theorems/05d5963a-d5b4-411a-978d-4b96b3fc4cbe
-- title:
--   `BookProof.NavierStokesGaugeY.genY_shifts_velocity` (i j : Fin 3) (p : NSAlg) : genY j (X (NSVar.u i) * p) - X (NSVar.u i) * genY j p = -(X (NSVar.uD i j) * p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.genY_shifts_velocity` (i j : Fin 3) (p : NSAlg) : genY j (X (NSVar.u i) * p) - X (NSVar.u i) * genY j p = -(X (NSVar.uD i j) * p)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.genY_shifts_velocity`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.genY_shifts_velocity
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.genY_shifts_velocity (i j : Fin 3) (p : NSAlg) :
    genY j (X (NSVar.u i) * p) - X (NSVar.u i) * genY j p = -(X (NSVar.uD i j) * p) := by sorry
