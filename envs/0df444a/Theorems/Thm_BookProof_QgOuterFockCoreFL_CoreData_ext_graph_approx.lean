-- Prove2me | Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_graph_approx
-- name    : BookProof.QgOuterFockCoreFL.CoreData.ext_graph_approx
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:19:38.812987+00:00
-- url     : https://prove2.me/theorems/46f8fec8-f5c5-4d5d-b9b9-0476ff2c3503
-- title:
--   `BookProof.QgOuterFockCoreFL.CoreData.ext_graph_approx` (x : d.C.dom) (ε : ℝ) (hε : 0 < ε) : ∃ y : d.C.dom, (y : F) ∈ d.C₀ ∧ ‖(y : F) - (x : F)‖ < ε ∧ ‖d.ext y - d.ext x‖ < ε
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFarisLavineOnly`.
--
--   `BookProof.QgOuterFockCoreFL.CoreData.ext_graph_approx` (x : d.C.dom) (ε : ℝ) (hε : 0 < ε) : ∃ y : d.C.dom, (y : F) ∈ d.C₀ ∧ ‖(y : F) - (x : F)‖ < ε ∧ ‖d.ext y - d.ext x‖ < ε
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockCoreFL.CoreData.ext_graph_approx`.

-- Generated from ChapterFarisLavineOnly.lean — theorem BookProof.QgOuterFockCoreFL.CoreData.ext_graph_approx
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterFarisLavineOnly
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterLeafGaps
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL


open scoped ENNReal

noncomputable section


open BookProof.FarisLavine


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]


variable (d : CoreData F)

theorem BookProof.QgOuterFockCoreFL.CoreData.ext_graph_approx (x : d.C.dom) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : d.C.dom, (y : F) ∈ d.C₀ ∧ ‖(y : F) - (x : F)‖ < ε ∧ ‖d.ext y - d.ext x‖ < ε := by sorry
