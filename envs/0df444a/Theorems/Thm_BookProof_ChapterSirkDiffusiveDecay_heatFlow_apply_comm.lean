-- Prove2me | Theorems.Thm_BookProof_ChapterSirkDiffusiveDecay_heatFlow_apply_comm
-- name    : BookProof.ChapterSirkDiffusiveDecay.heatFlow_apply_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-09T12:05:33.469686+00:00
-- url     : https://prove2.me/theorems/d05a3a34-4645-4b4a-8bb6-16316d78687d
-- title:
--   ChapterSirkDiffusiveDecay theorem
-- statement:
--   Theorem from ChapterSirkDiffusiveDecay.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkDiffusiveDecay.lean

-- Generated from ChapterSirkDiffusiveDecay.lean — theorem BookProof.ChapterSirkDiffusiveDecay.heatFlow_apply_comm
import Mathlib
import Definitions.Def_ChapterSirkDiffusiveDecay
open BookProof.ChapterSirkDiffusiveDecay









noncomputable section


open BookProof.ChapterH4
open Filter Topology NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkDiffusiveDecay.heatFlow_apply_comm (A : E →L[ℂ] E) (t : ℝ) (v : E) :
    heatFlow A t (A v) = A (heatFlow A t v) := by sorry
