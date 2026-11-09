-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_hermiteMvNorm_add_pvec
-- name    : BookProof.FullQuadratic.hermiteMvNorm_add_pvec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:30:25.166522+00:00
-- url     : https://prove2.me/theorems/468970be-d313-4946-8f8e-34d9109ad77c
-- title:
--   `BookProof.FullQuadratic.hermiteMvNorm_add_pvec` (i j : Fin d) (a : Fin d →₀ ℕ) : hermiteMvNorm (a + pvec i j) = hermiteMvNorm a * rcp a i j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.hermiteMvNorm_add_pvec` (i j : Fin d) (a : Fin d →₀ ℕ) : hermiteMvNorm (a + pvec i j) = hermiteMvNorm a * rcp a i j
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.hermiteMvNorm_add_pvec`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.hermiteMvNorm_add_pvec
import Definitions.Def_ChapterHermiteProductCore
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
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductBasis
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

theorem BookProof.FullQuadratic.hermiteMvNorm_add_pvec (i j : Fin d) (a : Fin d →₀ ℕ) :
    hermiteMvNorm (a + pvec i j) = hermiteMvNorm a * rcp a i j := by sorry
