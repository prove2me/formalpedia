-- Prove2me | Theorems.Thm_BookProof_ChapterLayerNorm_layerNorm_add_const
-- name    : BookProof.ChapterLayerNorm.layerNorm_add_const
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:25:05.463984+00:00
-- url     : https://prove2.me/theorems/4b905cc7-fa75-4dae-be36-215a4f3105e1
-- title:
--   `BookProof.ChapterLayerNorm.layerNorm_add_const` (hd : 0 < d) (x : Fin d → ℝ) (c : ℝ) (i : Fin d) : layerNorm (fun i => x i + c) i = layerNorm x i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLayerNorm`.
--
--   `BookProof.ChapterLayerNorm.layerNorm_add_const` (hd : 0 < d) (x : Fin d → ℝ) (c : ℝ) (i : Fin d) : layerNorm (fun i => x i + c) i = layerNorm x i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLayerNorm.layerNorm_add_const`.

-- Generated from ChapterLayerNorm.lean — theorem BookProof.ChapterLayerNorm.layerNorm_add_const
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

theorem BookProof.ChapterLayerNorm.layerNorm_add_const (hd : 0 < d) (x : Fin d → ℝ) (c : ℝ) (i : Fin d) :
    layerNorm (fun i => x i + c) i = layerNorm x i := by sorry
