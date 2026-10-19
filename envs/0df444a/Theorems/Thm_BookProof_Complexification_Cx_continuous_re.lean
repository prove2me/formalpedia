-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_continuous_re
-- name    : BookProof.Complexification.Cx.continuous_re
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:48:17.020374+00:00
-- url     : https://prove2.me/theorems/64f29b10-c8d6-44f4-a168-cb963799081f
-- title:
--   `BookProof.Complexification.Cx.continuous_re` : Continuous (Cx.re : Cx W → W)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1b`.
--
--   `BookProof.Complexification.Cx.continuous_re` : Continuous (Cx.re : Cx W → W)
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.continuous_re`.

-- Generated from ChapterA1b.lean — theorem BookProof.Complexification.Cx.continuous_re
import Definitions.Def_ChapterA
import Mathlib
import Definitions.Def_ChapterA1b
import Definitions.Def_Complexification
open BookProof.Complexification
open BookProof.Complexification


open scoped RealInnerProductSpace
open BookProof.ChapterA


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem BookProof.Complexification.Cx.continuous_re : Continuous (Cx.re : Cx W → W) := by sorry
