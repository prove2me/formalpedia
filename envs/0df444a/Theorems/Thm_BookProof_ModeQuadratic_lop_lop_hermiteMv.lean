-- Prove2me | Theorems.Thm_BookProof_ModeQuadratic_lop_lop_hermiteMv
-- name    : BookProof.ModeQuadratic.lop_lop_hermiteMv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:35:00.660202+00:00
-- url     : https://prove2.me/theorems/c8c59666-f1a0-467b-b97f-eeed1f635e35
-- title:
--   `BookProof.ModeQuadratic.lop_lop_hermiteMv` (t t' : ℂ) (i : Fin d) (a : Fin d →₀ ℕ) : lop t i (lop t' i (hermiteMv a)) = hermiteMv (a + Finsupp.single i 2) + (t * ((a i : ℂ) + 1) +
-- statement:
--   Prove the following Lean 4 theorem from `ChapterModeQuadraticEsa`.
--
--   `BookProof.ModeQuadratic.lop_lop_hermiteMv` (t t' : ℂ) (i : Fin d) (a : Fin d →₀ ℕ) : lop t i (lop t' i (hermiteMv a)) = hermiteMv (a + Finsupp.single i 2) + (t * ((a i : ℂ) + 1) + t' * (a i : ℂ)) • hermiteMv a + (t * t' * (a i : ℂ) * (((a i - 1 : ℕ) : ℂ))) • hermiteMv (a - Finsupp.single i 2)
--
--   Formalization note: Lean 4 identifier `BookProof.ModeQuadratic.lop_lop_hermiteMv`.

-- Generated from ChapterModeQuadraticEsa.lean — theorem BookProof.ModeQuadratic.lop_lop_hermiteMv
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.HermiteProductCore
open BookProof.ModeQuadratic



open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.CarlemanTwoStep
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ModeQuadratic.lop_lop_hermiteMv (t t' : ℂ) (i : Fin d) (a : Fin d →₀ ℕ) :
    lop t i (lop t' i (hermiteMv a))
      = hermiteMv (a + Finsupp.single i 2)
        + (t * ((a i : ℂ) + 1) + t' * (a i : ℂ)) • hermiteMv a
        + (t * t' * (a i : ℂ) * (((a i - 1 : ℕ) : ℂ))) • hermiteMv (a - Finsupp.single i 2) := by sorry
