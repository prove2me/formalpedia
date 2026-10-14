-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_cxMap_mul
-- name    : BookProof.Complexification.Cx.cxMap_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:38:56.80695+00:00
-- url     : https://prove2.me/theorems/7fc14862-439d-413c-aa12-7fbafbdef0f1
-- title:
--   `BookProof.Complexification.Cx.cxMap_mul` (m n : W →L[ℝ] W) : cxMap (m * n) = cxMap m * cxMap n
-- statement:
--   Prove the following Lean 4 theorem from `Complexification`.
--
--   `BookProof.Complexification.Cx.cxMap_mul` (m n : W →L[ℝ] W) : cxMap (m * n) = cxMap m * cxMap n
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.cxMap_mul`.

-- Generated from Complexification.lean — theorem BookProof.Complexification.Cx.cxMap_mul
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

theorem BookProof.Complexification.Cx.cxMap_mul (m n : W →L[ℝ] W) : cxMap (m * n) = cxMap m * cxMap n := by sorry
