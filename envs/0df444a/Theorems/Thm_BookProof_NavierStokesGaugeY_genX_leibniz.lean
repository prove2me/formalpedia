-- Prove2me | Theorems.Thm_BookProof_NavierStokesGaugeY_genX_leibniz
-- name    : BookProof.NavierStokesGaugeY.genX_leibniz
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:42:25.690976+00:00
-- url     : https://prove2.me/theorems/2f57168d-ff56-43e8-8a14-4c0b9e5d5216
-- title:
--   `BookProof.NavierStokesGaugeY.genX_leibniz` (j : Fin 3) (p q : NSAlg) : genX j (p * q) = genX j p * q + p * genX j q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesGaugeY`.
--
--   `BookProof.NavierStokesGaugeY.genX_leibniz` (j : Fin 3) (p q : NSAlg) : genX j (p * q) = genX j p * q + p * genX j q
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesGaugeY.genX_leibniz`.

-- Generated from ChapterNavierStokesGaugeY.lean — theorem BookProof.NavierStokesGaugeY.genX_leibniz
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NavierStokesGaugeY



open MvPolynomial BookProof.NavierStokesFlow

theorem BookProof.NavierStokesGaugeY.genX_leibniz (j : Fin 3) (p q : NSAlg) :
    genX j (p * q) = genX j p * q + p * genX j q := by sorry
