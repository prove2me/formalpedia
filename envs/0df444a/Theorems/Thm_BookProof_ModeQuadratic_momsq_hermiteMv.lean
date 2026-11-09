-- Prove2me | Theorems.Thm_BookProof_ModeQuadratic_momsq_hermiteMv
-- name    : BookProof.ModeQuadratic.momsq_hermiteMv
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T12:36:19.123573+00:00
-- url     : https://prove2.me/theorems/aa09ab6b-c2e3-4736-9ac1-dc6390dd0ab9
-- title:
--   `BookProof.ModeQuadratic.momsq_hermiteMv` (i : Fin d) (a : Fin d →₀ ℕ) : BookProof.YangMillsHermite.weylProd (momPoly i) (momPoly i) (hermiteMv a) = (-(1 / 4 : ℂ)) • hermiteMv (a +
-- statement:
--   Prove the following Lean 4 theorem from `ChapterModeQuadraticEsa`.
--
--   `BookProof.ModeQuadratic.momsq_hermiteMv` (i : Fin d) (a : Fin d →₀ ℕ) : BookProof.YangMillsHermite.weylProd (momPoly i) (momPoly i) (hermiteMv a) = (-(1 / 4 : ℂ)) • hermiteMv (a + Finsupp.single i 2) + ((2 * (a i : ℂ) + 1) / 4) • hermiteMv a + (-(1 / 4 : ℂ) * (a i : ℂ) * (((a i - 1 : ℕ) : ℂ))) • hermiteMv (a - Finsupp.single i 2)
--
--   Formalization note: Lean 4 identifier `BookProof.ModeQuadratic.momsq_hermiteMv`.

-- Generated from ChapterModeQuadraticEsa.lean — theorem BookProof.ModeQuadratic.momsq_hermiteMv
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

theorem BookProof.ModeQuadratic.momsq_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    BookProof.YangMillsHermite.weylProd (momPoly i) (momPoly i) (hermiteMv a)
      = (-(1 / 4 : ℂ)) • hermiteMv (a + Finsupp.single i 2)
        + ((2 * (a i : ℂ) + 1) / 4) • hermiteMv a
        + (-(1 / 4 : ℂ) * (a i : ℂ) * (((a i - 1 : ℕ) : ℂ)))
            • hermiteMv (a - Finsupp.single i 2) := by sorry
