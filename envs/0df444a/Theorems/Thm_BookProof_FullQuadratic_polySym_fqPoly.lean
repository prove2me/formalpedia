-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_polySym_fqPoly
-- name    : BookProof.FullQuadratic.polySym_fqPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-24T09:29:33.712457+00:00
-- url     : https://prove2.me/theorems/5d443afc-fe83-4282-85b0-31d4aef86f91
-- title:
--   `BookProof.FullQuadratic.polySym_fqPoly` (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) : BookProof.YangMillsHermite.PolySym (fqPoly P Q S b b')
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.polySym_fqPoly` (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) : BookProof.YangMillsHermite.PolySym (fqPoly P Q S b b')
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.polySym_fqPoly`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.polySym_fqPoly
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStep
import Definitions.Def_ChapterCarlemanSimplex
import Definitions.Def_ChapterModeQuadraticEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterSirkFinitePrecision
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.HermiteRelative
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
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.FullQuadratic.polySym_fqPoly (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) :
    BookProof.YangMillsHermite.PolySym (fqPoly P Q S b b') := by sorry
