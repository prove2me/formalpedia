-- Prove2me | Theorems.Thm_BookProof_ChapterLayerNorm_variance_smul
-- name    : BookProof.ChapterLayerNorm.variance_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:25:53.995285+00:00
-- url     : https://prove2.me/theorems/5e6382e4-dd34-4881-88de-cff3ac340813
-- title:
--   `BookProof.ChapterLayerNorm.variance_smul` (a : ℝ) (x : Fin d → ℝ) : variance (fun i => a * x i) = a ^ 2 * variance x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLayerNorm`.
--
--   `BookProof.ChapterLayerNorm.variance_smul` (a : ℝ) (x : Fin d → ℝ) : variance (fun i => a * x i) = a ^ 2 * variance x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLayerNorm.variance_smul`.

-- Generated from ChapterLayerNorm.lean — theorem BookProof.ChapterLayerNorm.variance_smul
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

theorem BookProof.ChapterLayerNorm.variance_smul (a : ℝ) (x : Fin d → ℝ) :
    variance (fun i => a * x i) = a ^ 2 * variance x := by sorry
