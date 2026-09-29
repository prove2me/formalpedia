-- Prove2me | Theorems.Thm_BookProof_ChapterSirkDiffusiveDecay_hasDerivAt_heatFlow_apply
-- name    : BookProof.ChapterSirkDiffusiveDecay.hasDerivAt_heatFlow_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-09T12:03:57.321329+00:00
-- url     : https://prove2.me/theorems/8eb9f7df-7191-4555-9ea2-d7344f2dd1d2
-- title:
--   ChapterSirkDiffusiveDecay theorem
-- statement:
--   Theorem from ChapterSirkDiffusiveDecay.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkDiffusiveDecay.lean

-- Generated from ChapterSirkDiffusiveDecay.lean — theorem BookProof.ChapterSirkDiffusiveDecay.hasDerivAt_heatFlow_apply
import Mathlib
import Definitions.Def_ChapterSirkDiffusiveDecay
open BookProof.ChapterSirkDiffusiveDecay









noncomputable section


open BookProof.ChapterH4
open Filter Topology NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkDiffusiveDecay.hasDerivAt_heatFlow_apply (A : E →L[ℂ] E) (v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => heatFlow A s v) (-(A (heatFlow A t v))) t := by sorry
