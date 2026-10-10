-- Prove2me | Theorems.Thm_BookProof_ChapterLayerNorm_sum_sq_sub_mean_eq
-- name    : BookProof.ChapterLayerNorm.sum_sq_sub_mean_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:23:49.990007+00:00
-- url     : https://prove2.me/theorems/760f2726-d895-4d6b-b6d3-f1dca55acdba
-- title:
--   `BookProof.ChapterLayerNorm.sum_sq_sub_mean_eq` (hd : 0 < d) (x : Fin d → ℝ) : ∑ i, (x i - mean x) ^ 2 = (d : ℝ) * variance x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLayerNorm`.
--
--   `BookProof.ChapterLayerNorm.sum_sq_sub_mean_eq` (hd : 0 < d) (x : Fin d → ℝ) : ∑ i, (x i - mean x) ^ 2 = (d : ℝ) * variance x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLayerNorm.sum_sq_sub_mean_eq`.

-- Generated from ChapterLayerNorm.lean — theorem BookProof.ChapterLayerNorm.sum_sq_sub_mean_eq
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterLayerNorm
import Definitions.Def_ChapterTotalVariance
open ChapterTotalVariance
open BookProof.ChapterLayerNorm


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {d : ℕ}

theorem BookProof.ChapterLayerNorm.sum_sq_sub_mean_eq (hd : 0 < d) (x : Fin d → ℝ) :
    ∑ i, (x i - mean x) ^ 2 = (d : ℝ) * variance x := by sorry
