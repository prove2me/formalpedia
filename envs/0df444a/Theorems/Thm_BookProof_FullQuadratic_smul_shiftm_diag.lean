-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_smul_shiftm_diag
-- name    : BookProof.FullQuadratic.smul_shiftm_diag
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:27:42.377703+00:00
-- url     : https://prove2.me/theorems/3cfec3c9-3ad1-442a-bb5e-f6578a84e8ef
-- title:
--   `BookProof.FullQuadratic.smul_shiftm_diag` (c : ℂ) (a : Fin d →₀ ℕ) (i : Fin d) : (c * (a i : ℂ)) • hermiteMv (shiftm a i i) = (c * (a i : ℂ)) • hermiteMv a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.smul_shiftm_diag` (c : ℂ) (a : Fin d →₀ ℕ) (i : Fin d) : (c * (a i : ℂ)) • hermiteMv (shiftm a i i) = (c * (a i : ℂ)) • hermiteMv a
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.smul_shiftm_diag`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.smul_shiftm_diag
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
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.HermiteProductCore
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

theorem BookProof.FullQuadratic.smul_shiftm_diag (c : ℂ) (a : Fin d →₀ ℕ) (i : Fin d) :
    (c * (a i : ℂ)) • hermiteMv (shiftm a i i) = (c * (a i : ℂ)) • hermiteMv a := by sorry
