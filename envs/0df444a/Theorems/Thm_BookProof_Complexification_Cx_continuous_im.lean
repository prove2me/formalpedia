-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_continuous_im
-- name    : BookProof.Complexification.Cx.continuous_im
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:48:17.918087+00:00
-- url     : https://prove2.me/theorems/2b7dd1e1-cead-40c1-be92-bde3706ed4cc
-- title:
--   `BookProof.Complexification.Cx.continuous_im` : Continuous (Cx.im : Cx W → W)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1b`.
--
--   `BookProof.Complexification.Cx.continuous_im` : Continuous (Cx.im : Cx W → W)
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.continuous_im`.

-- Generated from ChapterA1b.lean — theorem BookProof.Complexification.Cx.continuous_im
import Definitions.Def_ChapterA
import Mathlib
import Definitions.Def_ChapterA1b
import Definitions.Def_Complexification
open BookProof.Complexification
open BookProof.Complexification


open scoped RealInnerProductSpace
open BookProof.ChapterA


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem BookProof.Complexification.Cx.continuous_im : Continuous (Cx.im : Cx W → W) := by sorry
