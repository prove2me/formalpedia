-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionRetrieval_norm_headOutput_sub_le_of_margin
-- name    : BookProof.ChapterAttentionRetrieval.norm_headOutput_sub_le_of_margin
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:43:52.229301+00:00
-- url     : https://prove2.me/theorems/fc15570a-a32c-464d-b568-daa1726fe80b
-- title:
--   `BookProof.ChapterAttentionRetrieval.norm_headOutput_sub_le_of_margin` {beta delta C : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (v : Fin m → E) (j : Fin m) (hmargin : ∀ l, l ≠ j → s l +
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionRetrieval`.
--
--   `BookProof.ChapterAttentionRetrieval.norm_headOutput_sub_le_of_margin` {beta delta C : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (v : Fin m → E) (j : Fin m) (hmargin : ∀ l, l ≠ j → s l + delta ≤ s j) (hv : ∀ l, ‖v l‖ ≤ C) : ‖headOutput beta s v - v j‖ ≤ 2 * C * (((m : ℝ) - 1) * Real.exp (-(beta * delta)))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionRetrieval.norm_headOutput_sub_le_of_margin`.

-- Generated from ChapterAttentionRetrieval.lean — theorem BookProof.ChapterAttentionRetrieval.norm_headOutput_sub_le_of_margin
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionRetrieval
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionRetrieval


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionOutput

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionRetrieval.norm_headOutput_sub_le_of_margin {beta delta C : ℝ} (hb : 0 ≤ beta)
    (s : Fin m → ℝ) (v : Fin m → E) (j : Fin m)
    (hmargin : ∀ l, l ≠ j → s l + delta ≤ s j) (hv : ∀ l, ‖v l‖ ≤ C) :
    ‖headOutput beta s v - v j‖ ≤ 2 * C * (((m : ℝ) - 1) * Real.exp (-(beta * delta))) := by sorry
