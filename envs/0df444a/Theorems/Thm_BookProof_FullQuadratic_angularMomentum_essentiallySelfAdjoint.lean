-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_angularMomentum_essentiallySelfAdjoint
-- name    : BookProof.FullQuadratic.angularMomentum_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:32:32.591988+00:00
-- url     : https://prove2.me/theorems/d1dc7139-23f7-4e5e-8909-5864864bdb57
-- title:
--   `BookProof.FullQuadratic.angularMomentum_essentiallySelfAdjoint` (k l : Fin d) : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (fqOp 0 0 (rotMat k l) 0 0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.angularMomentum_essentiallySelfAdjoint` (k l : Fin d) : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (fqOp 0 0 (rotMat k l) 0 0)
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.angularMomentum_essentiallySelfAdjoint`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.angularMomentum_essentiallySelfAdjoint
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
import Definitions.Def_ChapterFarisLavineCore
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

theorem BookProof.FullQuadratic.angularMomentum_essentiallySelfAdjoint (k l : Fin d) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (fqOp 0 0 (rotMat k l) 0 0) := by sorry
