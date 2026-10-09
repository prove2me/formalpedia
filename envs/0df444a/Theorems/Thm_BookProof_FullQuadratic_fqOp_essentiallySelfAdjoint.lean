-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_fqOp_essentiallySelfAdjoint
-- name    : BookProof.FullQuadratic.fqOp_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T22:45:39.360687+00:00
-- url     : https://prove2.me/theorems/11388cb5-a488-4570-9649-f046ff9c8f22
-- title:
--   `BookProof.FullQuadratic.fqOp_essentiallySelfAdjoint` (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (fqOp P Q S b b')
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.fqOp_essentiallySelfAdjoint` (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (fqOp P Q S b b')
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.fqOp_essentiallySelfAdjoint`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.fqOp_essentiallySelfAdjoint
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
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
open BookProof.HermiteProductCore
open BookProof.FullQuadratic



open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.FullQuadratic.fqOp_essentiallySelfAdjoint (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (fqOp P Q S b b') := by sorry
