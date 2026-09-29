-- Prove2me | Theorems.Thm_BookProof_ChapterSirkDiffusiveDecay_hasDerivAt_heatFlow_normSq
-- name    : BookProof.ChapterSirkDiffusiveDecay.hasDerivAt_heatFlow_normSq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-09T12:04:40.505007+00:00
-- url     : https://prove2.me/theorems/766185f9-7746-4d20-ba4b-55a67f5aeeb8
-- title:
--   ChapterSirkDiffusiveDecay theorem
-- statement:
--   Theorem from ChapterSirkDiffusiveDecay.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkDiffusiveDecay.lean

-- Generated from ChapterSirkDiffusiveDecay.lean — theorem BookProof.ChapterSirkDiffusiveDecay.hasDerivAt_heatFlow_normSq
import Mathlib
import Definitions.Def_ChapterSirkDiffusiveDecay
open BookProof.ChapterSirkDiffusiveDecay









noncomputable section


open BookProof.ChapterH4
open Filter Topology NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkDiffusiveDecay.hasDerivAt_heatFlow_normSq (A : E →L[ℂ] E) (v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ‖heatFlow A s v‖ ^ 2)
      (-2 * (inner ℂ (heatFlow A t v) (A (heatFlow A t v)) : ℂ).re) t := by sorry
