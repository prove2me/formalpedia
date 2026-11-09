-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_add_sub_single_eq_shiftm
-- name    : BookProof.FullQuadratic.add_sub_single_eq_shiftm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:26:11.923119+00:00
-- url     : https://prove2.me/theorems/46f177de-39df-4206-bf5e-f6f8c7518074
-- title:
--   `BookProof.FullQuadratic.add_sub_single_eq_shiftm` {a : Fin d →₀ ℕ} {i j : Fin d} (hij : i ≠ j) : a + Finsupp.single j 1 - Finsupp.single i 1 = shiftm a j i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.add_sub_single_eq_shiftm` {a : Fin d →₀ ℕ} {i j : Fin d} (hij : i ≠ j) : a + Finsupp.single j 1 - Finsupp.single i 1 = shiftm a j i
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.add_sub_single_eq_shiftm`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.add_sub_single_eq_shiftm
import Definitions.Def_ChapterHermiteProductCore
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
import Definitions.Def_ChapterGaussCoreQuadBounds
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

theorem BookProof.FullQuadratic.add_sub_single_eq_shiftm {a : Fin d →₀ ℕ} {i j : Fin d} (hij : i ≠ j) :
    a + Finsupp.single j 1 - Finsupp.single i 1 = shiftm a j i := by sorry
