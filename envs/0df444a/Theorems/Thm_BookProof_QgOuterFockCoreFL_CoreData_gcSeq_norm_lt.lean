-- Prove2me | Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_gcSeq_norm_lt
-- name    : BookProof.QgOuterFockCoreFL.CoreData.gcSeq_norm_lt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T19:01:00.126551+00:00
-- url     : https://prove2.me/theorems/a7de092f-fe36-468a-b9df-47e2cb18227a
-- title:
--   The Lean 4 theorem `gcSeq_norm_lt` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `gcSeq_norm_lt` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockCoreFL.lean

-- Generated from ChapterQgOuterFockCoreFL.lean — theorem BookProof.QgOuterFockCoreFL.CoreData.gcSeq_norm_lt
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterHermiteProductCore
import Mathlib
import Definitions.Def_ChapterQgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (d : CoreData F)



open BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock
open BookProof.QgOuterFockFL
open BookProof.YangMillsFriedrichs
open BookProof.EsaClosure
open BookProof.QgHermiteOscillator
open BookProof.HermiteProductCore
open Filter Topology

noncomputable section

theorem BookProof.QgOuterFockCoreFL.CoreData.gcSeq_norm_lt (x : d.C.dom) (k : ℕ) :
    ‖((d.gcSeq x k : d.C.dom) : F) - (x : F)‖ < 1 / (k + 1) := by sorry
