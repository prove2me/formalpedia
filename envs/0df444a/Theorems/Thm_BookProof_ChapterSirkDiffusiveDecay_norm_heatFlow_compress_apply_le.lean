-- Prove2me | Theorems.Thm_BookProof_ChapterSirkDiffusiveDecay_norm_heatFlow_compress_apply_le
-- name    : BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_compress_apply_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-09T12:09:10.843499+00:00
-- url     : https://prove2.me/theorems/a5609f1b-8559-4839-ab4f-588423b87692
-- title:
--   ChapterSirkDiffusiveDecay theorem
-- statement:
--   Theorem from ChapterSirkDiffusiveDecay.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkDiffusiveDecay.lean

-- Generated from ChapterSirkDiffusiveDecay.lean — theorem BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_compress_apply_le
import Mathlib
import Definitions.Def_ChapterSirkDiffusiveDecay
open BookProof.ChapterSirkDiffusiveDecay









noncomputable section


open BookProof.ChapterH4
open Filter Topology NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_compress_apply_le (V : F →L[ℂ] E) (A : E →L[ℂ] E) {mu : ℝ}
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F) (hA : IsCoercive A mu) (x : F)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖heatFlow (compress V A) t x‖ ≤ Real.exp (-(mu * t)) * ‖x‖ := by sorry
