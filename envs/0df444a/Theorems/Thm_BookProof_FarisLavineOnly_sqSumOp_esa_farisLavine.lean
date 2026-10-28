-- Prove2me | Theorems.Thm_BookProof_FarisLavineOnly_sqSumOp_esa_farisLavine
-- name    : BookProof.FarisLavineOnly.sqSumOp_esa_farisLavine
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:20:07.541114+00:00
-- url     : https://prove2.me/theorems/f1d4358b-8fcc-4ef5-b788-daffa7da71cc
-- title:
--   `BookProof.FarisLavineOnly.sqSumOp_esa_farisLavine` (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) : EssentiallySelfAdjointOn (polyGaussCore (d := D)) (sqSumOp kappa v)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFarisLavineOnly`.
--
--   `BookProof.FarisLavineOnly.sqSumOp_esa_farisLavine` (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) : EssentiallySelfAdjointOn (polyGaussCore (d := D)) (sqSumOp kappa v)
--
--   Formalization note: Lean 4 identifier `BookProof.FarisLavineOnly.sqSumOp_esa_farisLavine`.

-- Generated from ChapterFarisLavineOnly.lean — theorem BookProof.FarisLavineOnly.sqSumOp_esa_farisLavine
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterSqSumOuterFamily
import Mathlib
import Definitions.Def_ChapterFarisLavineOnly
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductCore
open BookProof.QgOuterFock
open BookProof.QgOuterFockCoreFL


open scoped ENNReal

noncomputable section


open BookProof.FarisLavine


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]


variable (d : CoreData F)







open Finset
open BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.HermiteProductCore BookProof.QgHermiteOscillator
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL

variable {D : ℕ} {R : Type} [Fintype R]

theorem BookProof.FarisLavineOnly.sqSumOp_esa_farisLavine (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := D)) (sqSumOp kappa v) := by sorry
