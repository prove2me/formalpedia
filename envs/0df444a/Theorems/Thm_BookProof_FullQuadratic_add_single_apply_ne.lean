-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_add_single_apply_ne
-- name    : BookProof.FullQuadratic.add_single_apply_ne
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:26:42.763194+00:00
-- url     : https://prove2.me/theorems/32fa8ff2-3335-4849-bd59-3c4163ba808c
-- title:
--   `BookProof.FullQuadratic.add_single_apply_ne` {a : Fin d →₀ ℕ} {i j : Fin d} (hij : i ≠ j) : ((a + Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) = a i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.add_single_apply_ne` {a : Fin d →₀ ℕ} {i j : Fin d} (hij : i ≠ j) : ((a + Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) = a i
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.add_single_apply_ne`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.add_single_apply_ne
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

theorem BookProof.FullQuadratic.add_single_apply_ne {a : Fin d →₀ ℕ} {i j : Fin d} (hij : i ≠ j) :
    ((a + Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) = a i := by sorry
