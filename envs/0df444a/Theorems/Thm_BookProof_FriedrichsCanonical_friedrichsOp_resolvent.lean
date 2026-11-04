-- Prove2me | Theorems.Thm_BookProof_FriedrichsCanonical_friedrichsOp_resolvent
-- name    : BookProof.FriedrichsCanonical.friedrichsOp_resolvent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T13:46:33.712116+00:00
-- url     : https://prove2.me/theorems/7b00a813-f377-4046-8fdf-bc4afee3d14e
-- title:
--   `BookProof.FriedrichsCanonical.friedrichsOp_resolvent` (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) (u : F) : friedrichsOp P hdense ⟨friedrichsResolvent P u, resolvent_mem_fri
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsCanonical`.
--
--   `BookProof.FriedrichsCanonical.friedrichsOp_resolvent` (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) (u : F) : friedrichsOp P hdense ⟨friedrichsResolvent P u, resolvent_mem_friedrichsDomain P u⟩ = u - friedrichsResolvent P u
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsCanonical.friedrichsOp_resolvent`.

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.friedrichsOp_resolvent
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterVielbeinFiberFock
import Theorems.Thm_BookProof_FriedrichsCanonical_resolvent_mem_friedrichsDomain
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.QgOuterFockFL
open BookProof.FriedrichsCanonical



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.FriedrichsCanonical.friedrichsOp_resolvent (P : PosSymOp F) (hdense : Dense (P.dom : Set F)) (u : F) :
    friedrichsOp P hdense ⟨friedrichsResolvent P u, resolvent_mem_friedrichsDomain P u⟩
      = u - friedrichsResolvent P u := by sorry
