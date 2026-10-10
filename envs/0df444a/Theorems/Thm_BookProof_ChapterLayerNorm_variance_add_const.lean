-- Prove2me | Theorems.Thm_BookProof_ChapterLayerNorm_variance_add_const
-- name    : BookProof.ChapterLayerNorm.variance_add_const
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:24:47.429444+00:00
-- url     : https://prove2.me/theorems/e9913b32-8476-4931-8636-5991e7f090d3
-- title:
--   `BookProof.ChapterLayerNorm.variance_add_const` (hd : 0 < d) (x : Fin d → ℝ) (c : ℝ) : variance (fun i => x i + c) = variance x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLayerNorm`.
--
--   `BookProof.ChapterLayerNorm.variance_add_const` (hd : 0 < d) (x : Fin d → ℝ) (c : ℝ) : variance (fun i => x i + c) = variance x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLayerNorm.variance_add_const`.

-- Generated from ChapterLayerNorm.lean — theorem BookProof.ChapterLayerNorm.variance_add_const
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

theorem BookProof.ChapterLayerNorm.variance_add_const (hd : 0 < d) (x : Fin d → ℝ) (c : ℝ) :
    variance (fun i => x i + c) = variance x := by sorry
