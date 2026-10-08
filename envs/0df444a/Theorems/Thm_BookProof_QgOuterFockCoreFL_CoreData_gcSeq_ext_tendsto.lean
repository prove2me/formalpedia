-- Prove2me | Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_gcSeq_ext_tendsto
-- name    : BookProof.QgOuterFockCoreFL.CoreData.gcSeq_ext_tendsto
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T18:28:25.419411+00:00
-- url     : https://prove2.me/theorems/f8042d91-f08f-47c5-a2de-d8ac9c006d25
-- title:
--   The Lean 4 theorem `gcSeq_ext_tendsto` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `gcSeq_ext_tendsto` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockCoreFL.lean

-- Generated from ChapterQgOuterFockCoreFL.lean — theorem BookProof.QgOuterFockCoreFL.CoreData.gcSeq_ext_tendsto
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

theorem BookProof.QgOuterFockCoreFL.CoreData.gcSeq_ext_tendsto (x : d.C.dom) :
    Tendsto (fun k => d.ext (d.gcSeq x k)) atTop (𝓝 (d.ext x)) := by sorry
