-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentPositionSpace_gaussianPacket_inner_eq_one_iff
-- name    : BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_eq_one_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:04:40.724781+00:00
-- url     : https://prove2.me/theorems/03b226cf-513f-4a29-a78b-47fdc5eaa3cd
-- title:
--   `BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_eq_one_iff` (a b : ℝ) : (∫ x : ℝ, gaussianPacket a x * gaussianPacket b x) = 1 ↔ a = b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentPositionSpace`.
--
--   `BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_eq_one_iff` (a b : ℝ) : (∫ x : ℝ, gaussianPacket a x * gaussianPacket b x) = 1 ↔ a = b
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_eq_one_iff`.

-- Generated from ChapterCoherentPositionSpace.lean — theorem BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_eq_one_iff
import Definitions.Def_ChapterCoherentOverlap
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterCoherentPositionSpace
open BookProof.ChapterCoherentPositionSpace


open scoped BigOperators
open MeasureTheory

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxSharpness

theorem BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_eq_one_iff (a b : ℝ) :
    (∫ x : ℝ, gaussianPacket a x * gaussianPacket b x) = 1 ↔ a = b := by sorry
