-- Prove2me | Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_essentiallySelfAdjointOn
-- name    : BookProof.QgOuterFockCoreFL.CoreData.ext_essentiallySelfAdjointOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T19:20:08.914375+00:00
-- url     : https://prove2.me/theorems/9f5ef649-ec3d-4b2f-8bf5-cdecd7b203de
-- title:
--   The Lean 4 theorem `ext_essentiallySelfAdjointOn` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ext_essentiallySelfAdjointOn` in the `ChapterQgOuterFockCoreFL` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockCoreFL.lean

-- Generated from ChapterQgOuterFockCoreFL.lean — theorem BookProof.QgOuterFockCoreFL.CoreData.ext_essentiallySelfAdjointOn
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

theorem BookProof.QgOuterFockCoreFL.CoreData.ext_essentiallySelfAdjointOn (hsym : SymmetricOn d.C₀ d.H₀) {c : ℝ} (hc : 0 ≤ c)
    (hcomm : ∀ p : d.C₀, |commForm d.H₀ d.coreN p| ≤ c * quadForm d.coreN p) :
    EssentiallySelfAdjointOn d.C.dom d.ext := by sorry
