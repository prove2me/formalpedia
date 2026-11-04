-- Prove2me | Theorems.Thm_BookProof_NsFullLagrangian_detPoly_eval_testPt
-- name    : BookProof.NsFullLagrangian.detPoly_eval_testPt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T22:24:53.020396+00:00
-- url     : https://prove2.me/theorems/f4fb6d5e-41ba-4100-9a7b-d428943adb0d
-- title:
--   `BookProof.NsFullLagrangian.detPoly_eval_testPt` (p : Fin n) (t : ℝ) : eval (testPt p t) (detPoly p) = (t : ℂ) ^ 3
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullLagrangianFock`.
--
--   `BookProof.NsFullLagrangian.detPoly_eval_testPt` (p : Fin n) (t : ℝ) : eval (testPt p t) (detPoly p) = (t : ℂ) ^ 3
--
--   Formalization note: Lean 4 identifier `BookProof.NsFullLagrangian.detPoly_eval_testPt`.

-- Generated from ChapterNavierStokesFullLagrangianFock.lean — theorem BookProof.NsFullLagrangian.detPoly_eval_testPt
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

theorem BookProof.NsFullLagrangian.detPoly_eval_testPt (p : Fin n) (t : ℝ) :
    eval (testPt p t) (detPoly p) = (t : ℂ) ^ 3 := by sorry
