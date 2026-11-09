-- Prove2me | Theorems.Thm_BookProof_FullQuadratic_fqQuadPoly_rotMat
-- name    : BookProof.FullQuadratic.fqQuadPoly_rotMat
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T12:32:23.520529+00:00
-- url     : https://prove2.me/theorems/5e819870-5da7-4865-bde6-a8777fcdb6e7
-- title:
--   `BookProof.FullQuadratic.fqQuadPoly_rotMat` (k l : Fin d) : fqQuadPoly (d := d) 0 0 (rotMat k l) = BookProof.YangMillsHermite.weylProd (mulXPoly k) (momPoly l) - BookProof.YangMill
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFullQuadraticEsa`.
--
--   `BookProof.FullQuadratic.fqQuadPoly_rotMat` (k l : Fin d) : fqQuadPoly (d := d) 0 0 (rotMat k l) = BookProof.YangMillsHermite.weylProd (mulXPoly k) (momPoly l) - BookProof.YangMillsHermite.weylProd (mulXPoly l) (momPoly k)
--
--   Formalization note: Lean 4 identifier `BookProof.FullQuadratic.fqQuadPoly_rotMat`.

-- Generated from ChapterFullQuadraticEsa.lean — theorem BookProof.FullQuadratic.fqQuadPoly_rotMat
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
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.NavierStokesFlow.DifferentialL2
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

theorem BookProof.FullQuadratic.fqQuadPoly_rotMat (k l : Fin d) :
    fqQuadPoly (d := d) 0 0 (rotMat k l)
      = BookProof.YangMillsHermite.weylProd (mulXPoly k) (momPoly l)
        - BookProof.YangMillsHermite.weylProd (mulXPoly l) (momPoly k) := by sorry
