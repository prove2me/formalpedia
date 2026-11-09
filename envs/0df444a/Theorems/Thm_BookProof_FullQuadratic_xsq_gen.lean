-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_xsq_gen
-- name    : BookProof.FullQuadratic.xsq_gen
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:29:17.869573+00:00
-- url     : https://prove2.me/theorems/196bb2a3-3fd5-4b5d-be39-b53d14cb89a9
-- title:
--   `BookProof.FullQuadratic.xsq_gen` (i j : Fin d) (a : Fin d →₀ ℕ) : BookProof.YangMillsHermite.weylProd (mulXPoly i) (mulXPoly j) (hermiteMv a) = BookProof.YangMillsHermite.weylProd
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.xsq_gen` (i j : Fin d) (a : Fin d →₀ ℕ) : BookProof.YangMillsHermite.weylProd (mulXPoly i) (mulXPoly j) (hermiteMv a) = BookProof.YangMillsHermite.weylProd (lop 1 i) (lop 1 j) (hermiteMv a)
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.xsq_gen`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.xsq_gen
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
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
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.YangMillsHermite
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

theorem BookProof.FullQuadratic.xsq_gen (i j : Fin d) (a : Fin d →₀ ℕ) :
    BookProof.YangMillsHermite.weylProd (mulXPoly i) (mulXPoly j) (hermiteMv a)
      = BookProof.YangMillsHermite.weylProd (lop 1 i) (lop 1 j) (hermiteMv a) := by sorry
