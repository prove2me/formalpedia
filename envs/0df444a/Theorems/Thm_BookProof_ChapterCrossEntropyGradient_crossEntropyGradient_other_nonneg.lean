-- Prove2me | Theorems.Thm_BookProof_ChapterCrossEntropyGradient_crossEntropyGradient_other_nonneg
-- name    : BookProof.ChapterCrossEntropyGradient.crossEntropyGradient_other_nonneg
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:25:55.395487+00:00
-- url     : https://prove2.me/theorems/9cf69e3f-b683-4b54-803f-760b2c99967e
-- title:
--   `BookProof.ChapterCrossEntropyGradient.crossEntropyGradient_other_nonneg` {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) {y i : Fin m} (h : i ≠ y) : 0 ≤ crossEntropyGradient beta s y i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCrossEntropyGradient`.
--
--   `BookProof.ChapterCrossEntropyGradient.crossEntropyGradient_other_nonneg` {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) {y i : Fin m} (h : i ≠ y) : 0 ≤ crossEntropyGradient beta s y i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCrossEntropyGradient.crossEntropyGradient_other_nonneg`.

-- Generated from ChapterCrossEntropyGradient.lean — theorem BookProof.ChapterCrossEntropyGradient.crossEntropyGradient_other_nonneg
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterCrossEntropyGradient
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterCrossEntropyGradient


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterCrossEntropyGradient.crossEntropyGradient_other_nonneg {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ)
    {y i : Fin m} (h : i ≠ y) : 0 ≤ crossEntropyGradient beta s y i := by sorry
