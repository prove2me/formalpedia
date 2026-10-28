-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_fqOp_deficiencyTrivialAt
-- name    : BookProof.FullQuadratic.fqOp_deficiencyTrivialAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-24T09:09:36.277831+00:00
-- url     : https://prove2.me/theorems/08bcc34b-0be4-4af8-a1bb-7d2d5a46ebba
-- title:
--   `BookProof.FullQuadratic.fqOp_deficiencyTrivialAt` (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (polyGaussCore (d := d)) (fqOp P Q S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.fqOp_deficiencyTrivialAt` (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (polyGaussCore (d := d)) (fqOp P Q S b b') z
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.fqOp_deficiencyTrivialAt`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.fqOp_deficiencyTrivialAt
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStep
import Definitions.Def_ChapterCarlemanSimplex
import Definitions.Def_ChapterModeQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.FullQuadratic



open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.FullQuadratic.fqOp_deficiencyTrivialAt (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ)
    {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (polyGaussCore (d := d)) (fqOp P Q S b b') z := by sorry
