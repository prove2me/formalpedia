-- Prove2me | Theorems.Thm_BookProof_FarisLavineOnly_outerHam_esa_fl
-- name    : BookProof.FarisLavineOnly.outerHam_esa_fl
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T22:53:27.735199+00:00
-- url     : https://prove2.me/theorems/ecedeb6c-16d0-4d08-9ff4-85795c39512c
-- title:
--   `BookProof.FarisLavineOnly.outerHam_esa_fl` (F : SqFamily) : EssentiallySelfAdjointOn (outerCore F.dim) F.outerHam
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFarisLavineOnly`.
--
--   `BookProof.FarisLavineOnly.outerHam_esa_fl` (F : SqFamily) : EssentiallySelfAdjointOn (outerCore F.dim) F.outerHam
--
--   Formalization note: Lean 4 identifier `BookProof.FarisLavineOnly.outerHam_esa_fl`.

-- Generated from ChapterFarisLavineOnly.lean — theorem BookProof.FarisLavineOnly.outerHam_esa_fl
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterSqSumOuterFamily
import Mathlib
import Definitions.Def_ChapterFarisLavineOnly
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.HermiteProductCore
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
open BookProof.SqSumOuterFamily

theorem BookProof.FarisLavineOnly.outerHam_esa_fl (F : SqFamily) :
    EssentiallySelfAdjointOn (outerCore F.dim) F.outerHam := by sorry
