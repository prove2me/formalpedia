-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_genY_leibniz
-- name    : BookProof.NavierStokesGaugeY.genY_leibniz
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:42:16.016986+00:00
-- url     : https://prove2.me/theorems/b6684175-262a-4b36-aac8-26aedfd97937
-- title:
--   `BookProof.NavierStokesGaugeY.genY_leibniz` (j : Fin 3) (p q : NSAlg) : genY j (p * q) = genY j p * q + p * genY j q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.genY_leibniz` (j : Fin 3) (p q : NSAlg) : genY j (p * q) = genY j p * q + p * genY j q
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.genY_leibniz`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.genY_leibniz
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.genY_leibniz (j : Fin 3) (p q : NSAlg) :
    genY j (p * q) = genY j p * q + p * genY j q := by sorry
