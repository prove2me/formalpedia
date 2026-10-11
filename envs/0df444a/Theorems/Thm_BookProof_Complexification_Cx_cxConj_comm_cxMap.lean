-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_cxConj_comm_cxMap
-- name    : BookProof.Complexification.Cx.cxConj_comm_cxMap
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:39:23.670988+00:00
-- url     : https://prove2.me/theorems/027b91ee-e0ea-4a1d-bd22-5a38645fe2bb
-- title:
--   `BookProof.Complexification.Cx.cxConj_comm_cxMap` (m : W →L[ℝ] W) (x : Cx W) : cxConj (cxMap m x) = cxMap m (cxConj x)
-- statement:
--   Prove the following Lean 4 theorem from `Complexification`.
--
--   `BookProof.Complexification.Cx.cxConj_comm_cxMap` (m : W →L[ℝ] W) (x : Cx W) : cxConj (cxMap m x) = cxMap m (cxConj x)
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.cxConj_comm_cxMap`.

-- Generated from Complexification.lean — theorem BookProof.Complexification.Cx.cxConj_comm_cxMap
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

theorem BookProof.Complexification.Cx.cxConj_comm_cxMap (m : W →L[ℝ] W) (x : Cx W) :
    cxConj (cxMap m x) = cxMap m (cxConj x) := by sorry
