-- Prove2me | Theorems.Thm_BookProof_Complexification_cxConj_isConjugation
-- name    : BookProof.Complexification.cxConj_isConjugation
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:41:45.555978+00:00
-- url     : https://prove2.me/theorems/d9edf786-488d-4869-80c7-236a34936784
-- title:
--   `BookProof.Complexification.cxConj_isConjugation` [CompleteSpace W] (M : System ℝ W) : IsConjugation (cxSystem M) Cx.cxConj
-- statement:
--   Prove the following Lean 4 theorem from `Complexification`.
--
--   `BookProof.Complexification.cxConj_isConjugation` [CompleteSpace W] (M : System ℝ W) : IsConjugation (cxSystem M) Cx.cxConj
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.cxConj_isConjugation`.

-- Generated from Complexification.lean — theorem BookProof.Complexification.cxConj_isConjugation
import Mathlib
import Definitions.Def_Complexification
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterA.AntiUnitary
open BookProof.Complexification


open scoped RealInnerProductSpace
open RCLike


set_option linter.unusedSectionVars false

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem BookProof.Complexification.cxConj_isConjugation [CompleteSpace W] (M : System ℝ W) :
    IsConjugation (cxSystem M) Cx.cxConj := by sorry
