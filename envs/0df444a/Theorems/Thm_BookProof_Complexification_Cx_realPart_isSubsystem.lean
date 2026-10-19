-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_realPart_isSubsystem
-- name    : BookProof.Complexification.Cx.realPart_isSubsystem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:49:16.503986+00:00
-- url     : https://prove2.me/theorems/0faf108a-74d2-46fb-ba93-cdc75cc6ed78
-- title:
--   `BookProof.Complexification.Cx.realPart_isSubsystem` (M : System ℝ W) {X : Submodule ℂ (Cx W)} (hX : (cxSystem M).IsSubsystem X) : (M).IsSubsystem (realPart X)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1b`.
--
--   `BookProof.Complexification.Cx.realPart_isSubsystem` (M : System ℝ W) {X : Submodule ℂ (Cx W)} (hX : (cxSystem M).IsSubsystem X) : (M).IsSubsystem (realPart X)
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.realPart_isSubsystem`.

-- Generated from ChapterA1b.lean — theorem BookProof.Complexification.Cx.realPart_isSubsystem
import Mathlib
import Definitions.Def_ChapterA1b
import Definitions.Def_ChapterA
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_Complexification
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.Complexification
open BookProof.Complexification


open scoped RealInnerProductSpace
open BookProof.ChapterA


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

variable [CompleteSpace W]

theorem BookProof.Complexification.Cx.realPart_isSubsystem (M : System ℝ W) {X : Submodule ℂ (Cx W)}
    (hX : (cxSystem M).IsSubsystem X) : (M).IsSubsystem (realPart X) := by sorry
