-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_smul_I
-- name    : BookProof.Complexification.Cx.smul_I
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T18:39:27.742161+00:00
-- url     : https://prove2.me/theorems/6e0e2557-43f7-450d-aa02-2b3577e81f19
-- title:
--   `BookProof.Complexification.Cx.smul_I` (x : Cx W) : (Complex.I : ℂ) • x = ⟨-x.im, x.re⟩
-- statement:
--   Prove the following Lean 4 theorem from `Complexification`.
--
--   `BookProof.Complexification.Cx.smul_I` (x : Cx W) : (Complex.I : ℂ) • x = ⟨-x.im, x.re⟩
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.smul_I`.

-- Generated from Complexification.lean — theorem BookProof.Complexification.Cx.smul_I
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

theorem BookProof.Complexification.Cx.smul_I (x : Cx W) : (Complex.I : ℂ) • x = ⟨-x.im, x.re⟩ := by sorry
