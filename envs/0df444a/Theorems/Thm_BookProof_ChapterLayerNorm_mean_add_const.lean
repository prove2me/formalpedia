-- Prove2me | Theorems.Thm_BookProof_ChapterLayerNorm_mean_add_const
-- name    : BookProof.ChapterLayerNorm.mean_add_const
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:24:31.801198+00:00
-- url     : https://prove2.me/theorems/4871b9a5-2eb3-4bda-ae3c-ebe157ff63ce
-- title:
--   `BookProof.ChapterLayerNorm.mean_add_const` (hd : 0 < d) (x : Fin d → ℝ) (c : ℝ) : mean (fun i => x i + c) = mean x + c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLayerNorm`.
--
--   `BookProof.ChapterLayerNorm.mean_add_const` (hd : 0 < d) (x : Fin d → ℝ) (c : ℝ) : mean (fun i => x i + c) = mean x + c
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLayerNorm.mean_add_const`.

-- Generated from ChapterLayerNorm.lean — theorem BookProof.ChapterLayerNorm.mean_add_const
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

theorem BookProof.ChapterLayerNorm.mean_add_const (hd : 0 < d) (x : Fin d → ℝ) (c : ℝ) :
    mean (fun i => x i + c) = mean x + c := by sorry
