-- Prove2me | Theorems.Thm_BookProof_Complexification_Cx_lipschitz_re
-- name    : BookProof.Complexification.Cx.lipschitz_re
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:47:55.179448+00:00
-- url     : https://prove2.me/theorems/d04457c1-6349-4c77-be63-5fc07e4a1bbe
-- title:
--   `BookProof.Complexification.Cx.lipschitz_re` : LipschitzWith 1 (Cx.re : Cx W → W)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1b`.
--
--   `BookProof.Complexification.Cx.lipschitz_re` : LipschitzWith 1 (Cx.re : Cx W → W)
--
--   Formalization note: Lean 4 identifier `BookProof.Complexification.Cx.lipschitz_re`.

-- Generated from ChapterA1b.lean — theorem BookProof.Complexification.Cx.lipschitz_re
import Definitions.Def_ChapterA
import Mathlib
import Definitions.Def_ChapterA1b
import Definitions.Def_Complexification
open BookProof.Complexification
open BookProof.Complexification


open scoped RealInnerProductSpace
open BookProof.ChapterA


variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem BookProof.Complexification.Cx.lipschitz_re : LipschitzWith 1 (Cx.re : Cx W → W) := by sorry
