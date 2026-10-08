-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOutput_headOutput_eq_sum
-- name    : BookProof.ChapterAttentionOutput.headOutput_eq_sum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:33:12.144993+00:00
-- url     : https://prove2.me/theorems/96dee9d3-b01f-4a89-95ad-53887b933ef5
-- title:
--   `BookProof.ChapterAttentionOutput.headOutput_eq_sum` (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) : headOutput beta s v = ∑ j, scoreSoftmax beta s j • v j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOutput`.
--
--   `BookProof.ChapterAttentionOutput.headOutput_eq_sum` (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) : headOutput beta s v = ∑ j, scoreSoftmax beta s j • v j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOutput.headOutput_eq_sum`.

-- Generated from ChapterAttentionOutput.lean — theorem BookProof.ChapterAttentionOutput.headOutput_eq_sum
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutput


open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionOutput.headOutput_eq_sum (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) :
    headOutput beta s v = ∑ j, scoreSoftmax beta s j • v j := by sorry
