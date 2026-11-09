-- Prove2me | Theorems.Thm_BookProof_ModeQuadratic_xsq_hermiteMv
-- name    : BookProof.ModeQuadratic.xsq_hermiteMv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:36:39.609769+00:00
-- url     : https://prove2.me/theorems/1c452b93-3343-496f-8105-77cf7326f61c
-- title:
--   `BookProof.ModeQuadratic.xsq_hermiteMv` (i : Fin d) (a : Fin d →₀ ℕ) : BookProof.YangMillsHermite.weylProd (mulXPoly i) (mulXPoly i) (hermiteMv a) = (1 : ℂ) • hermiteMv (a + Finsup
-- statement:
--   Prove the following Lean 4 theorem from `ChapterModeQuadraticEsa`.
--
--   `BookProof.ModeQuadratic.xsq_hermiteMv` (i : Fin d) (a : Fin d →₀ ℕ) : BookProof.YangMillsHermite.weylProd (mulXPoly i) (mulXPoly i) (hermiteMv a) = (1 : ℂ) • hermiteMv (a + Finsupp.single i 2) + (2 * (a i : ℂ) + 1) • hermiteMv a + ((a i : ℂ) * (((a i - 1 : ℕ) : ℂ))) • hermiteMv (a - Finsupp.single i 2)
--
--   Formalization note: Lean 4 identifier `BookProof.ModeQuadratic.xsq_hermiteMv`.

-- Generated from ChapterModeQuadraticEsa.lean — theorem BookProof.ModeQuadratic.xsq_hermiteMv
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.YangMillsHermite
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

theorem BookProof.ModeQuadratic.xsq_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    BookProof.YangMillsHermite.weylProd (mulXPoly i) (mulXPoly i) (hermiteMv a)
      = (1 : ℂ) • hermiteMv (a + Finsupp.single i 2)
        + (2 * (a i : ℂ) + 1) • hermiteMv a
        + ((a i : ℂ) * (((a i - 1 : ℕ) : ℂ))) • hermiteMv (a - Finsupp.single i 2) := by sorry
