-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_genX_ccr_x
-- name    : BookProof.NavierStokesGaugeY.genX_ccr_x
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:24:12.696748+00:00
-- url     : https://prove2.me/theorems/93e6b1f1-ad21-4af3-b54d-6a8c8544b0ac
-- title:
--   `BookProof.NavierStokesGaugeY.genX_ccr_x` (j k : Fin 3) (p : NSAlg) : genX j (X (NSVar.x k) * p) - X (NSVar.x k) * genX j p = if NSVar.x j = NSVar.x k then p else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.genX_ccr_x` (j k : Fin 3) (p : NSAlg) : genX j (X (NSVar.x k) * p) - X (NSVar.x k) * genX j p = if NSVar.x j = NSVar.x k then p else 0
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.genX_ccr_x`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.genX_ccr_x
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.genX_ccr_x (j k : Fin 3) (p : NSAlg) :
    genX j (X (NSVar.x k) * p) - X (NSVar.x k) * genX j p
      = if NSVar.x j = NSVar.x k then p else 0 := by sorry
