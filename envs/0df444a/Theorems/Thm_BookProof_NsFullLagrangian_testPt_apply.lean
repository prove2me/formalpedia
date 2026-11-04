-- Prove2me | Theorems.Thm_BookProof_NsFullLagrangian_testPt_apply
-- name    : BookProof.NsFullLagrangian.testPt_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T22:24:42.334904+00:00
-- url     : https://prove2.me/theorems/c934d581-0f09-4574-a365-d89a76afda16
-- title:
--   `BookProof.NsFullLagrangian.testPt_apply` (p : Fin n) (t : ℝ) (k : Fin 36) : testPt p t (ycoord p k) = locVal t k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullLagrangianFock`.
--
--   `BookProof.NsFullLagrangian.testPt_apply` (p : Fin n) (t : ℝ) (k : Fin 36) : testPt p t (ycoord p k) = locVal t k
--
--   Formalization note: Lean 4 identifier `BookProof.NsFullLagrangian.testPt_apply`.

-- Generated from ChapterNavierStokesFullLagrangianFock.lean — theorem BookProof.NsFullLagrangian.testPt_apply
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterQg3DGaugeFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterNavierStokesFullLagrangianFock
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterQgOuterFockInteractionFL



open MvPolynomial
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.StoneBridge BookProof.QgOuterFockFL
open BookProof.QgOuterFockInteractionFL
open BookProof.ChapterStoneResolvent

noncomputable section

variable {n : ℕ}

theorem BookProof.NsFullLagrangian.testPt_apply (p : Fin n) (t : ℝ) (k : Fin 36) :
    testPt p t (ycoord p k) = locVal t k := by sorry
