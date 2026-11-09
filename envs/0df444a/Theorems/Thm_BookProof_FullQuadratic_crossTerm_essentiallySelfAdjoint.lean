-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_crossTerm_essentiallySelfAdjoint
-- name    : BookProof.FullQuadratic.crossTerm_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:31:25.592124+00:00
-- url     : https://prove2.me/theorems/7ca08f2e-3419-4173-8678-55ca753e722d
-- title:
--   `BookProof.FullQuadratic.crossTerm_essentiallySelfAdjoint` (S : Fin d → Fin d → ℝ) : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (fqOp 0 0 S 0 0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.crossTerm_essentiallySelfAdjoint` (S : Fin d → Fin d → ℝ) : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (fqOp 0 0 S 0 0)
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.crossTerm_essentiallySelfAdjoint`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.crossTerm_essentiallySelfAdjoint
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

theorem BookProof.FullQuadratic.crossTerm_essentiallySelfAdjoint (S : Fin d → Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (fqOp 0 0 S 0 0) := by sorry
