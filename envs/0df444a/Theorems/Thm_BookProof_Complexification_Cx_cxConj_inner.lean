-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_cxConj_inner
-- name    : BookProof.Complexification.Cx.cxConj_inner
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:38:01.590253+00:00
-- url     : https://prove2.me/theorems/8d9b0d4b-9188-47df-a9ad-23a0326ade41
-- title:
--   `BookProof.Complexification.Cx.cxConj_inner` (x y : Cx W) : inner ℂ (cxConj x) (cxConj y) = starRingEnd ℂ (inner ℂ x y)
-- statement:
--   Prove the following Lean 4 theorem from `Complexification`.
--
--   `BookProof.Complexification.Cx.cxConj_inner` (x y : Cx W) : inner ℂ (cxConj x) (cxConj y) = starRingEnd ℂ (inner ℂ x y)
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.cxConj_inner`.

-- Generated from Complexification.lean — theorem BookProof.Complexification.Cx.cxConj_inner
import Mathlib
import Definitions.Def_Complexification
open BookProof.Complexification
open BookProof.Complexification


open scoped RealInnerProductSpace
open RCLike


set_option linter.unusedSectionVars false

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem BookProof.Complexification.Cx.cxConj_inner (x y : Cx W) :
    inner ℂ (cxConj x) (cxConj y) = starRingEnd ℂ (inner ℂ x y) := by sorry
