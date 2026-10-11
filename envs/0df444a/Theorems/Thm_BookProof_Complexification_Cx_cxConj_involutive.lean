-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_cxConj_involutive
-- name    : BookProof.Complexification.Cx.cxConj_involutive
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:38:11.187976+00:00
-- url     : https://prove2.me/theorems/ba0efee5-bd95-40dd-8bd3-3b1249e9472e
-- title:
--   `BookProof.Complexification.Cx.cxConj_involutive` (x : Cx W) : cxConj (cxConj x) = x
-- statement:
--   Prove the following Lean 4 theorem from `Complexification`.
--
--   `BookProof.Complexification.Cx.cxConj_involutive` (x : Cx W) : cxConj (cxConj x) = x
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.cxConj_involutive`.

-- Generated from Complexification.lean — theorem BookProof.Complexification.Cx.cxConj_involutive
import Mathlib
import Definitions.Def_Complexification
import Definitions.Def_ChapterQgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.Complexification
open BookProof.Complexification


open scoped RealInnerProductSpace
open RCLike


set_option linter.unusedSectionVars false

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem BookProof.Complexification.Cx.cxConj_involutive (x : Cx W) : cxConj (cxConj x) = x := by sorry
