-- Prove2me | Theorems.Thm_BookProof_ModeQuadratic_mqOp_deficiencyTrivialAt
-- name    : BookProof.ModeQuadratic.mqOp_deficiencyTrivialAt
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T12:38:21.797212+00:00
-- url     : https://prove2.me/theorems/837e8fba-aa11-416f-83b3-d8c02a7394d6
-- title:
--   `BookProof.ModeQuadratic.mqOp_deficiencyTrivialAt` (p q s b b' : Fin d → ℝ) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (polyGaussCore (d := d)) (mqOp p q s b b') z
-- statement:
--   Prove the following Lean 4 theorem from `ChapterModeQuadraticEsa`.
--
--   `BookProof.ModeQuadratic.mqOp_deficiencyTrivialAt` (p q s b b' : Fin d → ℝ) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (polyGaussCore (d := d)) (mqOp p q s b b') z
--
--   Formalization note: Lean 4 identifier `BookProof.ModeQuadratic.mqOp_deficiencyTrivialAt`.

-- Generated from ChapterModeQuadraticEsa.lean — theorem BookProof.ModeQuadratic.mqOp_deficiencyTrivialAt
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
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductBasis
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

theorem BookProof.ModeQuadratic.mqOp_deficiencyTrivialAt (p q s b b' : Fin d → ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (polyGaussCore (d := d)) (mqOp p q s b b') z := by sorry
