-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOutputVariance_headOutput_minimizes
-- name    : BookProof.ChapterAttentionOutputVariance.headOutput_minimizes
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:38:29.835986+00:00
-- url     : https://prove2.me/theorems/62ff76bc-e206-4504-9105-0a965039ac4e
-- title:
--   `BookProof.ChapterAttentionOutputVariance.headOutput_minimizes` (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) (i : Fin m) (c : E) : ∑ j, scoreSoftmax beta s j * ‖v j - headOutput beta
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOutputVariance`.
--
--   `BookProof.ChapterAttentionOutputVariance.headOutput_minimizes` (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) (i : Fin m) (c : E) : ∑ j, scoreSoftmax beta s j * ‖v j - headOutput beta s v‖ ^ 2 ≤ ∑ j, scoreSoftmax beta s j * ‖v j - c‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOutputVariance.headOutput_minimizes`.

-- Generated from ChapterAttentionOutputVariance.lean — theorem BookProof.ChapterAttentionOutputVariance.headOutput_minimizes
import Definitions.Def_ChapterObservableExpectation
import Mathlib
import Definitions.Def_ChapterAttentionOutputVariance
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutputVariance


open scoped BigOperators RealInnerProductSpace

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterAttentionOutputVariance.headOutput_minimizes (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) (i : Fin m) (c : E) :
    ∑ j, scoreSoftmax beta s j * ‖v j - headOutput beta s v‖ ^ 2
      ≤ ∑ j, scoreSoftmax beta s j * ‖v j - c‖ ^ 2 := by sorry
