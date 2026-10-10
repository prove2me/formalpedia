-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_genY_ccr_y
-- name    : BookProof.NavierStokesGaugeY.genY_ccr_y
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:43:00.502982+00:00
-- url     : https://prove2.me/theorems/b16b5c34-c555-4495-8872-340129cb0fb7
-- title:
--   `BookProof.NavierStokesGaugeY.genY_ccr_y` (j k : Fin 3) (p : NSAlg) : genY j (X (NSVar.y k) * p) - X (NSVar.y k) * genY j p = if j = k then p else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.genY_ccr_y` (j k : Fin 3) (p : NSAlg) : genY j (X (NSVar.y k) * p) - X (NSVar.y k) * genY j p = if j = k then p else 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.genY_ccr_y`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.genY_ccr_y
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.genY_ccr_y (j k : Fin 3) (p : NSAlg) :
    genY j (X (NSVar.y k) * p) - X (NSVar.y k) * genY j p = if j = k then p else 0 := by sorry
