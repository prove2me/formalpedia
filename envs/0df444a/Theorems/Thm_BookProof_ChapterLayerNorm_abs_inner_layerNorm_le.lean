-- Prove2me | Theorems.Thm_BookProof_ChapterLayerNorm_abs_inner_layerNorm_le
-- name    : BookProof.ChapterLayerNorm.abs_inner_layerNorm_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:26:12.979985+00:00
-- url     : https://prove2.me/theorems/ae8e3a6a-d790-47ec-b62f-c51980071893
-- title:
--   `BookProof.ChapterLayerNorm.abs_inner_layerNorm_le` (hd : 0 < d) {x y : Fin d → ℝ} (hx : 0 < variance x) (hy : 0 < variance y) : |∑ i, layerNorm x i * layerNorm y i| ≤ (d : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLayerNorm`.
--
--   `BookProof.ChapterLayerNorm.abs_inner_layerNorm_le` (hd : 0 < d) {x y : Fin d → ℝ} (hx : 0 < variance x) (hy : 0 < variance y) : |∑ i, layerNorm x i * layerNorm y i| ≤ (d : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLayerNorm.abs_inner_layerNorm_le`.

-- Generated from ChapterLayerNorm.lean — theorem BookProof.ChapterLayerNorm.abs_inner_layerNorm_le
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

theorem BookProof.ChapterLayerNorm.abs_inner_layerNorm_le (hd : 0 < d) {x y : Fin d → ℝ} (hx : 0 < variance x)
    (hy : 0 < variance y) :
    |∑ i, layerNorm x i * layerNorm y i| ≤ (d : ℝ) := by sorry
