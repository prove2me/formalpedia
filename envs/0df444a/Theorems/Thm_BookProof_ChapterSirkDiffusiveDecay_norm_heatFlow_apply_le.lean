-- Prove2me | Theorems.Thm_BookProof_ChapterSirkDiffusiveDecay_norm_heatFlow_apply_le
-- name    : BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_apply_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-09T12:08:32.438988+00:00
-- url     : https://prove2.me/theorems/81036b03-cb2a-4922-acde-a9725f16df7b
-- title:
--   ChapterSirkDiffusiveDecay theorem
-- statement:
--   Theorem from ChapterSirkDiffusiveDecay.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkDiffusiveDecay.lean

-- Generated from ChapterSirkDiffusiveDecay.lean — theorem BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_apply_le
import Mathlib
import Definitions.Def_ChapterSirkDiffusiveDecay
open BookProof.ChapterSirkDiffusiveDecay









noncomputable section


open BookProof.ChapterH4
open Filter Topology NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_apply_le (A : E →L[ℂ] E) {mu : ℝ} (hA : IsCoercive A mu) (v : E)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖heatFlow A t v‖ ≤ Real.exp (-(mu * t)) * ‖v‖ := by sorry
