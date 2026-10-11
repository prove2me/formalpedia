-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxSharpness_tendsto_exp_mul_neg
-- name    : BookProof.ChapterSoftmaxSharpness.tendsto_exp_mul_neg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:36:51.703568+00:00
-- url     : https://prove2.me/theorems/6b66fb43-cef6-4cb2-8c96-4f581c79f80a
-- title:
--   `BookProof.ChapterSoftmaxSharpness.tendsto_exp_mul_neg` (c : ℝ) (hc : c < 0) : Tendsto (fun b : ℝ => Real.exp (b * c)) atTop (𝓝 0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxSharpness`.
--
--   `BookProof.ChapterSoftmaxSharpness.tendsto_exp_mul_neg` (c : ℝ) (hc : c < 0) : Tendsto (fun b : ℝ => Real.exp (b * c)) atTop (𝓝 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxSharpness.tendsto_exp_mul_neg`.

-- Generated from ChapterSoftmaxSharpness.lean — theorem BookProof.ChapterSoftmaxSharpness.tendsto_exp_mul_neg
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxSharpness.tendsto_exp_mul_neg (c : ℝ) (hc : c < 0) :
    Tendsto (fun b : ℝ => Real.exp (b * c)) atTop (𝓝 0) := by sorry
