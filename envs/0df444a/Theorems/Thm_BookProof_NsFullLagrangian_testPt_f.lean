-- Prove2me | Theorems.Thm_BookProof_NsFullLagrangian_testPt_f
-- name    : BookProof.NsFullLagrangian.testPt_f
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T22:25:09.775213+00:00
-- url     : https://prove2.me/theorems/bb3cc6e9-cc99-4d4b-bfe8-1641e457c936
-- title:
--   `BookProof.NsFullLagrangian.testPt_f` (p : Fin n) (t : ℝ) (i j : Fin 3) : testPt p t (ycoord p (fIdx i j)) = if i = j then (t : ℂ) else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullLagrangianFock`.
--
--   `BookProof.NsFullLagrangian.testPt_f` (p : Fin n) (t : ℝ) (i j : Fin 3) : testPt p t (ycoord p (fIdx i j)) = if i = j then (t : ℂ) else 0
--
--   Formalization note: Lean 4 identifier `BookProof.NsFullLagrangian.testPt_f`.

-- Generated from ChapterNavierStokesFullLagrangianFock.lean — theorem BookProof.NsFullLagrangian.testPt_f
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

theorem BookProof.NsFullLagrangian.testPt_f (p : Fin n) (t : ℝ) (i j : Fin 3) :
    testPt p t (ycoord p (fIdx i j)) = if i = j then (t : ℂ) else 0 := by sorry
