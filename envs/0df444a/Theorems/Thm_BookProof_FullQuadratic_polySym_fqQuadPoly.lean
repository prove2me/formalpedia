-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_polySym_fqQuadPoly
-- name    : BookProof.FullQuadratic.polySym_fqQuadPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T12:28:52.519196+00:00
-- url     : https://prove2.me/theorems/fcce1e70-0df8-4f00-9892-b9f05e854bde
-- title:
--   `BookProof.FullQuadratic.polySym_fqQuadPoly` (P Q S : Fin d → Fin d → ℝ) : BookProof.YangMillsHermite.PolySym (fqQuadPoly P Q S)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.polySym_fqQuadPoly` (P Q S : Fin d → Fin d → ℝ) : BookProof.YangMillsHermite.PolySym (fqQuadPoly P Q S)
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.polySym_fqQuadPoly`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.polySym_fqQuadPoly
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
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

theorem BookProof.FullQuadratic.polySym_fqQuadPoly (P Q S : Fin d → Fin d → ℝ) :
    BookProof.YangMillsHermite.PolySym (fqQuadPoly P Q S) := by sorry
