-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_fqOp_symmetric
-- name    : BookProof.FullQuadratic.fqOp_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-24T09:09:27.18298+00:00
-- url     : https://prove2.me/theorems/433e489b-1a8b-43a2-b9c8-f1bd7296980a
-- title:
--   `BookProof.FullQuadratic.fqOp_symmetric` (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) : SymmetricOn (polyGaussCore (d := d)) (fqOp P Q S b b')
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.fqOp_symmetric` (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) : SymmetricOn (polyGaussCore (d := d)) (fqOp P Q S b b')
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.fqOp_symmetric`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.fqOp_symmetric
import Definitions.Def_ChapterHermiteProductBasis
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
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.FullQuadratic.fqOp_symmetric (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) :
    SymmetricOn (polyGaussCore (d := d)) (fqOp P Q S b b') := by sorry
