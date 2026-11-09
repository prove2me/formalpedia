-- Prove2me | Theorems.Thm_BookProof_ModeQuadratic_polySym_mqQuadPoly
-- name    : BookProof.ModeQuadratic.polySym_mqQuadPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:34:56.966499+00:00
-- url     : https://prove2.me/theorems/6652fca4-09a5-429b-817a-e681eb53d489
-- title:
--   `BookProof.ModeQuadratic.polySym_mqQuadPoly` (p q s : Fin d → ℝ) : BookProof.YangMillsHermite.PolySym (mqQuadPoly p q s)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterModeQuadraticEsa`.
--
--   `BookProof.ModeQuadratic.polySym_mqQuadPoly` (p q s : Fin d → ℝ) : BookProof.YangMillsHermite.PolySym (mqQuadPoly p q s)
--
--   Formalization note: Lean 4 identifier `BookProof.ModeQuadratic.polySym_mqQuadPoly`.

-- Generated from ChapterModeQuadraticEsa.lean — theorem BookProof.ModeQuadratic.polySym_mqQuadPoly
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterSirkFinitePrecision
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.NavierStokesFlow.DifferentialL2
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

theorem BookProof.ModeQuadratic.polySym_mqQuadPoly (p q s : Fin d → ℝ) :
    BookProof.YangMillsHermite.PolySym (mqQuadPoly p q s) := by sorry
