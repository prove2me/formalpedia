-- Prove2me | Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_gcSeq_op_norm_lt
-- name    : BookProof.QgOuterFockCoreFL.CoreData.gcSeq_op_norm_lt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T19:01:08.665443+00:00
-- url     : https://prove2.me/theorems/5c05fde8-643e-4cba-85ee-619d721f5750
-- title:
--   The Lean 4 theorem `gcSeq_op_norm_lt` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `gcSeq_op_norm_lt` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockCoreFL.lean

-- Generated from ChapterQgOuterFockCoreFL.lean — theorem BookProof.QgOuterFockCoreFL.CoreData.gcSeq_op_norm_lt
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

theorem BookProof.QgOuterFockCoreFL.CoreData.gcSeq_op_norm_lt (x : d.C.dom) (k : ℕ) :
    ‖d.C.op (d.gcSeq x k) - d.C.op x‖ < 1 / (k + 1) := by sorry
