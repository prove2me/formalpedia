-- Prove2me | Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_commForm_le
-- name    : BookProof.QgOuterFockCoreFL.CoreData.ext_commForm_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T19:13:40.078073+00:00
-- url     : https://prove2.me/theorems/700d4856-cb21-46aa-8f27-7cf40c4f684e
-- title:
--   The Lean 4 theorem `ext_commForm_le` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ext_commForm_le` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockCoreFL.lean

-- Generated from ChapterQgOuterFockCoreFL.lean — theorem BookProof.QgOuterFockCoreFL.CoreData.ext_commForm_le
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

theorem BookProof.QgOuterFockCoreFL.CoreData.ext_commForm_le {c : ℝ}
    (hcomm : ∀ p : d.C₀, |commForm d.H₀ d.coreN p| ≤ c * quadForm d.coreN p)
    (x : d.C.dom) : |commForm d.ext d.C.op x| ≤ c * quadForm d.C.op x := by sorry
