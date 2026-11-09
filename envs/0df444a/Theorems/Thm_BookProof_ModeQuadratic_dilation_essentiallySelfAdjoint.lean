-- Prove2me | Theorems.Thm_BookProof_ModeQuadratic_dilation_essentiallySelfAdjoint
-- name    : BookProof.ModeQuadratic.dilation_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T12:39:35.850359+00:00
-- url     : https://prove2.me/theorems/d0b1bb55-4354-477d-85f0-514688a80d8b
-- title:
--   `BookProof.ModeQuadratic.dilation_essentiallySelfAdjoint` : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (mqOp 0 0 1 0 0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterModeQuadraticEsa`.
--
--   `BookProof.ModeQuadratic.dilation_essentiallySelfAdjoint` : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (mqOp 0 0 1 0 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ModeQuadratic.dilation_essentiallySelfAdjoint`.

-- Generated from ChapterModeQuadraticEsa.lean — theorem BookProof.ModeQuadratic.dilation_essentiallySelfAdjoint
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
import Definitions.Def_ChapterFarisLavineCore
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

theorem BookProof.ModeQuadratic.dilation_essentiallySelfAdjoint :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (mqOp 0 0 1 0 0) := by sorry
