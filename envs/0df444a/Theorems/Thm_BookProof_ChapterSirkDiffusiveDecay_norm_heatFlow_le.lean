-- Prove2me | Theorems.Thm_BookProof_ChapterSirkDiffusiveDecay_norm_heatFlow_le
-- name    : BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-09T12:09:46.323978+00:00
-- url     : https://prove2.me/theorems/73a84675-f621-4570-9804-eb1e72a7697a
-- title:
--   ChapterSirkDiffusiveDecay theorem
-- statement:
--   Theorem from ChapterSirkDiffusiveDecay.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkDiffusiveDecay.lean

-- Generated from ChapterSirkDiffusiveDecay.lean — theorem BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_le
import Mathlib
import Definitions.Def_ChapterSirkDiffusiveDecay
open BookProof.ChapterSirkDiffusiveDecay









noncomputable section


open BookProof.ChapterH4
open Filter Topology NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_le (A : E →L[ℂ] E) {mu : ℝ} (hA : IsCoercive A mu) {t : ℝ} (ht : 0 ≤ t) :
    ‖heatFlow A t‖ ≤ Real.exp (-(mu * t)) := by sorry
