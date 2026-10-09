-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_ofReal_add
-- name    : BookProof.Complexification.Cx.ofReal_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T09:33:20.96289+00:00
-- url     : https://prove2.me/theorems/20794515-4d01-4eee-93a3-2d653d4060dc
-- title:
--   `BookProof.Complexification.Cx.ofReal_add` (a b : W) : ofReal (a + b) = ofReal a + ofReal b
-- statement:
--   Prove the following Lean 4 theorem from `Complexification`.
--
--   `BookProof.Complexification.Cx.ofReal_add` (a b : W) : ofReal (a + b) = ofReal a + ofReal b
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.ofReal_add`.

-- Generated from Complexification.lean — theorem BookProof.Complexification.Cx.ofReal_add
import Mathlib
import Definitions.Def_Complexification
import Definitions.Def_ChapterQgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.Complexification
open BookProof.Complexification.Cx


open scoped RealInnerProductSpace
open RCLike


set_option linter.unusedSectionVars false

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem BookProof.Complexification.Cx.ofReal_add (a b : W) : ofReal (a + b) = ofReal a + ofReal b := by sorry
