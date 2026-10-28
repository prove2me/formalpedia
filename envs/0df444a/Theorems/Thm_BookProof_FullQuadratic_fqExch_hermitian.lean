-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_fqExch_hermitian
-- name    : BookProof.FullQuadratic.fqExch_hermitian
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-24T09:29:34.169553+00:00
-- url     : https://prove2.me/theorems/309bb4cf-ee8b-46f3-8766-0236a41fd757
-- title:
--   `BookProof.FullQuadratic.fqExch_hermitian` (P Q S : Fin d → Fin d → ℝ) (i j : Fin d) : (starRingEnd ℂ) (fqExch P Q S i j) = fqExch P Q S j i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.fqExch_hermitian` (P Q S : Fin d → Fin d → ℝ) (i j : Fin d) : (starRingEnd ℂ) (fqExch P Q S i j) = fqExch P Q S j i
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.fqExch_hermitian`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.fqExch_hermitian
import Definitions.Def_ChapterHermiteProductCore
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
import Definitions.Def_ChapterGaussCoreQuadBounds
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

theorem BookProof.FullQuadratic.fqExch_hermitian (P Q S : Fin d → Fin d → ℝ) (i j : Fin d) :
    (starRingEnd ℂ) (fqExch P Q S i j) = fqExch P Q S j i := by sorry
