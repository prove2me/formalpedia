-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentPositionSpace_gaussianPacket_inner
-- name    : BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:04:01.243242+00:00
-- url     : https://prove2.me/theorems/5f1efa0c-b286-45b2-813b-62ba0922de69
-- title:
--   `BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner` (a b : ℝ) : (∫ x : ℝ, gaussianPacket a x * gaussianPacket b x) = Real.exp (-(a - b) ^ 2 / 4)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentPositionSpace`.
--
--   `BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner` (a b : ℝ) : (∫ x : ℝ, gaussianPacket a x * gaussianPacket b x) = Real.exp (-(a - b) ^ 2 / 4)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner`.

-- Generated from ChapterCoherentPositionSpace.lean — theorem BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner
import Definitions.Def_ChapterCoherentOverlap
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterCoherentPositionSpace
open BookProof.ChapterCoherentPositionSpace


open scoped BigOperators
open MeasureTheory

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxSharpness

theorem BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner (a b : ℝ) :
    (∫ x : ℝ, gaussianPacket a x * gaussianPacket b x) = Real.exp (-(a - b) ^ 2 / 4) := by sorry
