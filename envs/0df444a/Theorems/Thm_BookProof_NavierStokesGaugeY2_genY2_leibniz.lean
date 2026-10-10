-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY2_genY2_leibniz
-- name    : BookProof.NavierStokesGaugeY2.genY2_leibniz
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:43:23.208321+00:00
-- url     : https://prove2.me/theorems/0b87a81a-c73e-465b-8611-e22929e634ba
-- title:
--   `BookProof.NavierStokesGaugeY2.genY2_leibniz` (j : Fin 3) (p q : NSAlg) : genY2 j (p * q) = genY2 j p * q + p * genY2 j q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY2`.
--
--   `BookProof.NavierStokesGaugeY2.genY2_leibniz` (j : Fin 3) (p q : NSAlg) : genY2 j (p * q) = genY2 j p * q + p * genY2 j q
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY2.genY2_leibniz`.

-- Generated from ChapterNavierStokesGaugeY2.lean — theorem BookProof.NavierStokesGaugeY2.genY2_leibniz
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY
open BookProof.NavierStokesGaugeY2



open MvPolynomial BookProof.NavierStokesGaugeY

theorem BookProof.NavierStokesGaugeY2.genY2_leibniz (j : Fin 3) (p q : NSAlg) :
    genY2 j (p * q) = genY2 j p * q + p * genY2 j q := by sorry
