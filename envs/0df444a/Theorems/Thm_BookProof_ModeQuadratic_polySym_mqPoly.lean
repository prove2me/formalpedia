-- Prove2me | Theorems.Thm_BookProof_ModeQuadratic_polySym_mqPoly
-- name    : BookProof.ModeQuadratic.polySym_mqPoly
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T12:35:51.131777+00:00
-- url     : https://prove2.me/theorems/733ca1aa-a447-41ba-a4a1-5b210b7de544
-- title:
--   `BookProof.ModeQuadratic.polySym_mqPoly` (p q s b b' : Fin d → ℝ) : BookProof.YangMillsHermite.PolySym (mqPoly p q s b b')
-- statement:
--   Prove the following Lean 4 theorem from `ChapterModeQuadraticEsa`.
--
--   `BookProof.ModeQuadratic.polySym_mqPoly` (p q s b b' : Fin d → ℝ) : BookProof.YangMillsHermite.PolySym (mqPoly p q s b b')
--
--   Formalization note: Lean 4 identifier `BookProof.ModeQuadratic.polySym_mqPoly`.

-- Generated from ChapterModeQuadraticEsa.lean — theorem BookProof.ModeQuadratic.polySym_mqPoly
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterSirkFinitePrecision
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.HermiteRelative
open BookProof.SirkFinitePrecision
open BookProof.SirkFinitePrecision.CertInterval
open BookProof.YangMillsHermite
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

theorem BookProof.ModeQuadratic.polySym_mqPoly (p q s b b' : Fin d → ℝ) :
    BookProof.YangMillsHermite.PolySym (mqPoly p q s b b') := by sorry
