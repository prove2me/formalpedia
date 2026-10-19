-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_eq_ofReal_add_smul
-- name    : BookProof.Complexification.Cx.eq_ofReal_add_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:48:37.051443+00:00
-- url     : https://prove2.me/theorems/35c4a0af-673d-4302-9cad-51c079e723b3
-- title:
--   `BookProof.Complexification.Cx.eq_ofReal_add_smul` (x : Cx W) : x = ofReal x.re + (Complex.I : ℂ) • ofReal x.im
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1b`.
--
--   `BookProof.Complexification.Cx.eq_ofReal_add_smul` (x : Cx W) : x = ofReal x.re + (Complex.I : ℂ) • ofReal x.im
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.eq_ofReal_add_smul`.

-- Generated from ChapterA1b.lean — theorem BookProof.Complexification.Cx.eq_ofReal_add_smul
import Definitions.Def_ChapterA
import Mathlib
import Definitions.Def_ChapterA1b
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_Complexification
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.Complexification
open BookProof.Complexification


open scoped RealInnerProductSpace
open BookProof.ChapterA


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem BookProof.Complexification.Cx.eq_ofReal_add_smul (x : Cx W) : x = ofReal x.re + (Complex.I : ℂ) • ofReal x.im := by sorry
