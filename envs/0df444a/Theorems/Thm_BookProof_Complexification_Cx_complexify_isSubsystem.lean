-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_complexify_isSubsystem
-- name    : BookProof.Complexification.Cx.complexify_isSubsystem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:49:10.051982+00:00
-- url     : https://prove2.me/theorems/1692611f-52da-45ee-9d43-6e6bbc61a889
-- title:
--   `BookProof.Complexification.Cx.complexify_isSubsystem` (M : System ℝ W) {Y : Submodule ℝ W} (hY : (M).IsSubsystem Y) : (cxSystem M).IsSubsystem (complexify Y)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1b`.
--
--   `BookProof.Complexification.Cx.complexify_isSubsystem` (M : System ℝ W) {Y : Submodule ℝ W} (hY : (M).IsSubsystem Y) : (cxSystem M).IsSubsystem (complexify Y)
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.complexify_isSubsystem`.

-- Generated from ChapterA1b.lean — theorem BookProof.Complexification.Cx.complexify_isSubsystem
import Mathlib
import Definitions.Def_ChapterA1b
import Definitions.Def_ChapterA
import Definitions.Def_Complexification
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.Complexification
open BookProof.Complexification.Cx


open scoped RealInnerProductSpace
open BookProof.ChapterA


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

variable [CompleteSpace W]

theorem BookProof.Complexification.Cx.complexify_isSubsystem (M : System ℝ W) {Y : Submodule ℝ W}
    (hY : (M).IsSubsystem Y) : (cxSystem M).IsSubsystem (complexify Y) := by sorry
