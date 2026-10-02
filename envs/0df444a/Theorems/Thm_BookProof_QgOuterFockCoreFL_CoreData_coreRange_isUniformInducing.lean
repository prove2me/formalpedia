-- Prove2me | Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_coreRange_isUniformInducing
-- name    : BookProof.QgOuterFockCoreFL.CoreData.coreRange_isUniformInducing
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-01T18:53:42.850951+00:00
-- url     : https://prove2.me/theorems/2e661f8c-74c1-4e1c-9941-2aecba25d50f
-- title:
--   The Lean 4 theorem `coreRange_isUniformInducing` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coreRange_isUniformInducing` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockCoreFL.lean

-- Generated from ChapterQgOuterFockCoreFL.lean — theorem BookProof.QgOuterFockCoreFL.CoreData.coreRange_isUniformInducing
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

theorem BookProof.QgOuterFockCoreFL.CoreData.coreRange_isUniformInducing : IsUniformInducing (d.coreRange.subtypeL) := by sorry
