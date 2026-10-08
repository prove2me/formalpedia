-- Prove2me | Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_commForm_tendsto
-- name    : BookProof.QgOuterFockCoreFL.CoreData.ext_commForm_tendsto
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T18:55:10.897165+00:00
-- url     : https://prove2.me/theorems/010a2124-6875-4b87-8223-2549f57f6bb4
-- title:
--   The Lean 4 theorem `ext_commForm_tendsto` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ext_commForm_tendsto` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockCoreFL.lean

-- Generated from ChapterQgOuterFockCoreFL.lean — theorem BookProof.QgOuterFockCoreFL.CoreData.ext_commForm_tendsto
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

theorem BookProof.QgOuterFockCoreFL.CoreData.ext_commForm_tendsto (x : d.C.dom) :
    Tendsto (fun k => commForm d.ext d.C.op (d.gcSeq x k)) atTop
      (𝓝 (commForm d.ext d.C.op x)) := by sorry
