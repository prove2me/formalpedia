-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_inner_im
-- name    : BookProof.Complexification.Cx.inner_im
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:37:57.209909+00:00
-- url     : https://prove2.me/theorems/99feb880-05a2-4598-98a7-387f60d87800
-- title:
--   `BookProof.Complexification.Cx.inner_im` (x y : Cx W) : RCLike.im (inner ℂ x y) = inner ℝ x.re y.im - inner ℝ x.im y.re
-- statement:
--   Prove the following Lean 4 theorem from `Complexification`.
--
--   `BookProof.Complexification.Cx.inner_im` (x y : Cx W) : RCLike.im (inner ℂ x y) = inner ℝ x.re y.im - inner ℝ x.im y.re
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.inner_im`.

-- Generated from Complexification.lean — theorem BookProof.Complexification.Cx.inner_im
import Mathlib
import Definitions.Def_Complexification
open BookProof.Complexification
open BookProof.Complexification


open scoped RealInnerProductSpace
open RCLike


set_option linter.unusedSectionVars false

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem BookProof.Complexification.Cx.inner_im (x y : Cx W) :
    RCLike.im (inner ℂ x y) = inner ℝ x.re y.im - inner ℝ x.im y.re := by sorry
