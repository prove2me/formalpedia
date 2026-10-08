-- Prove2me | Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_quadForm_tendsto
-- name    : BookProof.QgOuterFockCoreFL.CoreData.quadForm_tendsto
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T18:28:56.243927+00:00
-- url     : https://prove2.me/theorems/90360369-a952-4f57-b850-5640b2a7d021
-- title:
--   The Lean 4 theorem `quadForm_tendsto` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadForm_tendsto` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockCoreFL.lean

-- Generated from ChapterQgOuterFockCoreFL.lean — theorem BookProof.QgOuterFockCoreFL.CoreData.quadForm_tendsto
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
import Definitions.Def_ChapterFarisLavineCore
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL

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

theorem BookProof.QgOuterFockCoreFL.CoreData.quadForm_tendsto (x : d.C.dom) :
    Tendsto (fun k => quadForm d.C.op (d.gcSeq x k)) atTop (𝓝 (quadForm d.C.op x)) := by sorry
