-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_ofReal_fixed
-- name    : BookProof.Complexification.Cx.ofReal_fixed
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:38:32.891705+00:00
-- url     : https://prove2.me/theorems/9d43e07b-6369-47f3-ad38-ab6d93d45f0a
-- title:
--   `BookProof.Complexification.Cx.ofReal_fixed` (w : W) : cxConj (ofReal w) = ofReal w
-- statement:
--   Prove the following Lean 4 theorem from `Complexification`.
--
--   `BookProof.Complexification.Cx.ofReal_fixed` (w : W) : cxConj (ofReal w) = ofReal w
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.ofReal_fixed`.

-- Generated from Complexification.lean — theorem BookProof.Complexification.Cx.ofReal_fixed
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

theorem BookProof.Complexification.Cx.ofReal_fixed (w : W) : cxConj (ofReal w) = ofReal w := by sorry
