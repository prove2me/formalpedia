-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentPositionSpace_gaussianPacket_inner_sq_eq_coherentOverlap
-- name    : BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_sq_eq_coherentOverlap
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:04:47.728643+00:00
-- url     : https://prove2.me/theorems/6c029271-0303-4cb0-8080-f7d18f8903ef
-- title:
--   `BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_sq_eq_coherentOverlap` (a b : ℝ) : (∫ x : ℝ, gaussianPacket a x * gaussianPacket b x) ^ 2 = coherentOverlap (WithLp.toL
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentPositionSpace`.
--
--   `BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_sq_eq_coherentOverlap` (a b : ℝ) : (∫ x : ℝ, gaussianPacket a x * gaussianPacket b x) ^ 2 = coherentOverlap (WithLp.toLp 2 (fun _ => a) : EuclideanSpace ℝ (Fin 1)) (WithLp.toLp 2 (fun _ => b))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_sq_eq_coherentOverlap`.

-- Generated from ChapterCoherentPositionSpace.lean — theorem BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_sq_eq_coherentOverlap
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterCoherentPositionSpace
import Definitions.Def_ChapterCoherentOverlap
import Definitions.Def_ChapterHermiteProductCore
open BookProof.ChapterCoherentOverlap
open BookProof.HermiteProductCore
open BookProof.ChapterCoherentPositionSpace


open scoped BigOperators
open MeasureTheory

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxSharpness

theorem BookProof.ChapterCoherentPositionSpace.gaussianPacket_inner_sq_eq_coherentOverlap (a b : ℝ) :
    (∫ x : ℝ, gaussianPacket a x * gaussianPacket b x) ^ 2
      = coherentOverlap (WithLp.toLp 2 (fun _ => a) : EuclideanSpace ℝ (Fin 1))
          (WithLp.toLp 2 (fun _ => b)) := by sorry
