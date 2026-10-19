-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_lipschitz_im
-- name    : BookProof.Complexification.Cx.lipschitz_im
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:48:02.306358+00:00
-- url     : https://prove2.me/theorems/1a32f9e0-cdce-4901-9398-5aa2da8cf96d
-- title:
--   `BookProof.Complexification.Cx.lipschitz_im` : LipschitzWith 1 (Cx.im : Cx W → W)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1b`.
--
--   `BookProof.Complexification.Cx.lipschitz_im` : LipschitzWith 1 (Cx.im : Cx W → W)
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.lipschitz_im`.

-- Generated from ChapterA1b.lean — theorem BookProof.Complexification.Cx.lipschitz_im
import Definitions.Def_ChapterA
import Mathlib
import Definitions.Def_ChapterA1b
import Definitions.Def_Complexification
open BookProof.Complexification
open BookProof.Complexification


open scoped RealInnerProductSpace
open BookProof.ChapterA


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem BookProof.Complexification.Cx.lipschitz_im : LipschitzWith 1 (Cx.im : Cx W → W) := by sorry
