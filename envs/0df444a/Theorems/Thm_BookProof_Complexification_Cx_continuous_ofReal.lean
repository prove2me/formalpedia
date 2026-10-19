-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_continuous_ofReal
-- name    : BookProof.Complexification.Cx.continuous_ofReal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:48:27.030985+00:00
-- url     : https://prove2.me/theorems/6ffe1be5-4ac1-43c0-9b81-0ad6c8277eee
-- title:
--   `BookProof.Complexification.Cx.continuous_ofReal` : Continuous (Cx.ofReal : W → Cx W)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1b`.
--
--   `BookProof.Complexification.Cx.continuous_ofReal` : Continuous (Cx.ofReal : W → Cx W)
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.continuous_ofReal`.

-- Generated from ChapterA1b.lean — theorem BookProof.Complexification.Cx.continuous_ofReal
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

theorem BookProof.Complexification.Cx.continuous_ofReal : Continuous (Cx.ofReal : W → Cx W) := by sorry
