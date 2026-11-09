-- Prove2me | Theorems.Thm_BookProof_ModeQuadratic_mqOp_symmetric
-- name    : BookProof.ModeQuadratic.mqOp_symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T12:35:43.343471+00:00
-- url     : https://prove2.me/theorems/78562bef-405a-475f-aaca-9d299942ae46
-- title:
--   `BookProof.ModeQuadratic.mqOp_symmetric` (p q s b b' : Fin d → ℝ) : SymmetricOn (polyGaussCore (d := d)) (mqOp p q s b b')
-- statement:
--   Prove the following Lean 4 theorem from `ChapterModeQuadraticEsa`.
--
--   `BookProof.ModeQuadratic.mqOp_symmetric` (p q s b b' : Fin d → ℝ) : SymmetricOn (polyGaussCore (d := d)) (mqOp p q s b b')
--
--   Formalization note: Lean 4 identifier `BookProof.ModeQuadratic.mqOp_symmetric`.

-- Generated from ChapterModeQuadraticEsa.lean — theorem BookProof.ModeQuadratic.mqOp_symmetric
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

theorem BookProof.ModeQuadratic.mqOp_symmetric (p q s b b' : Fin d → ℝ) :
    SymmetricOn (polyGaussCore (d := d)) (mqOp p q s b b') := by sorry
