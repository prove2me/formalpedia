-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_cxConj_fixed_iff
-- name    : BookProof.Complexification.Cx.cxConj_fixed_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:38:37.535224+00:00
-- url     : https://prove2.me/theorems/6f249f27-6e9e-4bd0-87b6-bf0505781766
-- title:
--   `BookProof.Complexification.Cx.cxConj_fixed_iff` (x : Cx W) : cxConj x = x ↔ x.im = 0
-- statement:
--   Prove the following Lean 4 theorem from `Complexification`.
--
--   `BookProof.Complexification.Cx.cxConj_fixed_iff` (x : Cx W) : cxConj x = x ↔ x.im = 0
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.cxConj_fixed_iff`.

-- Generated from Complexification.lean — theorem BookProof.Complexification.Cx.cxConj_fixed_iff
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

theorem BookProof.Complexification.Cx.cxConj_fixed_iff (x : Cx W) : cxConj x = x ↔ x.im = 0 := by sorry
