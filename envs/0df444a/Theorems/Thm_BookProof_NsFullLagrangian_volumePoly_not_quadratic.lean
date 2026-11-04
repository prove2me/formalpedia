-- Prove2me | Theorems.Thm_BookProof_NsFullLagrangian_volumePoly_not_quadratic
-- name    : BookProof.NsFullLagrangian.volumePoly_not_quadratic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T22:24:34.60565+00:00
-- url     : https://prove2.me/theorems/ceac89ae-9171-42cc-abe5-19e811b9b08b
-- title:
--   `BookProof.NsFullLagrangian.volumePoly_not_quadratic` (p : Fin n) : ¬ ∃ a b c : ℂ, ∀ t : ℝ, eval (testPt p t) (volumePoly p) = a * (t : ℂ) ^ 2 + b * (t : ℂ) + c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullLagrangianFock`.
--
--   `BookProof.NsFullLagrangian.volumePoly_not_quadratic` (p : Fin n) : ¬ ∃ a b c : ℂ, ∀ t : ℝ, eval (testPt p t) (volumePoly p) = a * (t : ℂ) ^ 2 + b * (t : ℂ) + c
--
--   Formalization note: Lean 4 identifier `BookProof.NsFullLagrangian.volumePoly_not_quadratic`.

-- Generated from ChapterNavierStokesFullLagrangianFock.lean — theorem BookProof.NsFullLagrangian.volumePoly_not_quadratic
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

theorem BookProof.NsFullLagrangian.volumePoly_not_quadratic (p : Fin n) :
    ¬ ∃ a b c : ℂ, ∀ t : ℝ,
        eval (testPt p t) (volumePoly p) = a * (t : ℂ) ^ 2 + b * (t : ℂ) + c := by sorry
