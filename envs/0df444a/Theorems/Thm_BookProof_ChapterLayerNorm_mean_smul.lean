-- Prove2me | Theorems.Thm_BookProof_ChapterLayerNorm_mean_smul
-- name    : BookProof.ChapterLayerNorm.mean_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:25:24.797987+00:00
-- url     : https://prove2.me/theorems/2eaaccc6-d388-4ff0-ba5b-4fca3d027932
-- title:
--   `BookProof.ChapterLayerNorm.mean_smul` (a : ℝ) (x : Fin d → ℝ) : mean (fun i => a * x i) = a * mean x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLayerNorm`.
--
--   `BookProof.ChapterLayerNorm.mean_smul` (a : ℝ) (x : Fin d → ℝ) : mean (fun i => a * x i) = a * mean x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLayerNorm.mean_smul`.

-- Generated from ChapterLayerNorm.lean — theorem BookProof.ChapterLayerNorm.mean_smul
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

theorem BookProof.ChapterLayerNorm.mean_smul (a : ℝ) (x : Fin d → ℝ) : mean (fun i => a * x i) = a * mean x := by sorry
