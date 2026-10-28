-- Prove2me | Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_esa_on_core
-- name    : BookProof.QgOuterFockCoreFL.CoreData.esa_on_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:20:00.613746+00:00
-- url     : https://prove2.me/theorems/35a18647-3617-462b-bf45-2179f792d608
-- title:
--   `BookProof.QgOuterFockCoreFL.CoreData.esa_on_core` (hsym : SymmetricOn d.C₀ d.H₀) {c : ℝ} (hc : 0 ≤ c) (hcomm : ∀ p : d.C₀, |commForm d.H₀ d.coreN p| ≤ c * quadForm d.coreN p) : Es
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFarisLavineOnly`.
--
--   `BookProof.QgOuterFockCoreFL.CoreData.esa_on_core` (hsym : SymmetricOn d.C₀ d.H₀) {c : ℝ} (hc : 0 ≤ c) (hcomm : ∀ p : d.C₀, |commForm d.H₀ d.coreN p| ≤ c * quadForm d.coreN p) : EssentiallySelfAdjointOn d.C₀ d.H₀
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockCoreFL.CoreData.esa_on_core`.

-- Generated from ChapterFarisLavineOnly.lean — theorem BookProof.QgOuterFockCoreFL.CoreData.esa_on_core
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterFarisLavineOnly
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterLeafGaps
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL


open scoped ENNReal

noncomputable section


open BookProof.FarisLavine


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]


variable (d : CoreData F)

theorem BookProof.QgOuterFockCoreFL.CoreData.esa_on_core (hsym : SymmetricOn d.C₀ d.H₀) {c : ℝ} (hc : 0 ≤ c)
    (hcomm : ∀ p : d.C₀, |commForm d.H₀ d.coreN p| ≤ c * quadForm d.coreN p) :
    EssentiallySelfAdjointOn d.C₀ d.H₀ := by sorry
