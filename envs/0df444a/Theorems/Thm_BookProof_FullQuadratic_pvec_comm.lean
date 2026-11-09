-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_pvec_comm
-- name    : BookProof.FullQuadratic.pvec_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:25:24.352232+00:00
-- url     : https://prove2.me/theorems/bee3eb76-281b-44f6-b507-9582d820d154
-- title:
--   `BookProof.FullQuadratic.pvec_comm` (i j : Fin d) : pvec (d := d) i j = pvec j i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.pvec_comm` (i j : Fin d) : pvec (d := d) i j = pvec j i
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.pvec_comm`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.pvec_comm
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.FullQuadratic



open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.CarlemanTwoStep
open BookProof.CarlemanSimplex
open BookProof.ModeQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.FullQuadratic.pvec_comm (i j : Fin d) : pvec (d := d) i j = pvec j i := by sorry
