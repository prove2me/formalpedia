-- Prove2me | Theorems.Thm_BookProof_FarisLavineOnly_secHam_esa_fl
-- name    : BookProof.FarisLavineOnly.secHam_esa_fl
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T22:53:35.856746+00:00
-- url     : https://prove2.me/theorems/32b7f999-36ec-4350-b3b3-4f66a15648db
-- title:
--   `BookProof.FarisLavineOnly.secHam_esa_fl` (F : SqFamily) (n : ℕ) : EssentiallySelfAdjointOn (polyGaussCore (d := F.dim n)) (F.secHam n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFarisLavineOnly`.
--
--   `BookProof.FarisLavineOnly.secHam_esa_fl` (F : SqFamily) (n : ℕ) : EssentiallySelfAdjointOn (polyGaussCore (d := F.dim n)) (F.secHam n)
--
--   Formalization note: Lean 4 identifier `BookProof.FarisLavineOnly.secHam_esa_fl`.

-- Generated from ChapterFarisLavineOnly.lean — theorem BookProof.FarisLavineOnly.secHam_esa_fl
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

theorem BookProof.FarisLavineOnly.secHam_esa_fl (F : SqFamily) (n : ℕ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := F.dim n)) (F.secHam n) := by sorry
