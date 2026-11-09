-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_weylProd_smul_apply
-- name    : BookProof.FullQuadratic.weylProd_smul_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:28:12.395946+00:00
-- url     : https://prove2.me/theorems/4cec1f94-124c-4fd6-9ec6-4be8431d045b
-- title:
--   `BookProof.FullQuadratic.weylProd_smul_apply` (c c' : ℂ) (A B : Module.End ℂ (MvPolynomial (Fin d) ℂ)) (p : MvPolynomial (Fin d) ℂ) : BookProof.YangMillsHermite.weylProd (c • A) (c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.weylProd_smul_apply` (c c' : ℂ) (A B : Module.End ℂ (MvPolynomial (Fin d) ℂ)) (p : MvPolynomial (Fin d) ℂ) : BookProof.YangMillsHermite.weylProd (c • A) (c' • B) p = (c * c') • BookProof.YangMillsHermite.weylProd A B p
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.weylProd_smul_apply`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.weylProd_smul_apply
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
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.YangMillsHermite
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

theorem BookProof.FullQuadratic.weylProd_smul_apply (c c' : ℂ) (A B : Module.End ℂ (MvPolynomial (Fin d) ℂ))
    (p : MvPolynomial (Fin d) ℂ) :
    BookProof.YangMillsHermite.weylProd (c • A) (c' • B) p
      = (c * c') • BookProof.YangMillsHermite.weylProd A B p := by sorry
