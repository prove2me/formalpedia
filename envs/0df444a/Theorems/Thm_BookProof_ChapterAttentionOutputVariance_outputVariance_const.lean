-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOutputVariance_outputVariance_const
-- name    : BookProof.ChapterAttentionOutputVariance.outputVariance_const
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:38:04.448982+00:00
-- url     : https://prove2.me/theorems/6b031503-3092-427a-b82c-8600c5767377
-- title:
--   `BookProof.ChapterAttentionOutputVariance.outputVariance_const` (p : Fin m → ℝ) (hp : ∑ j, p j = 1) (w : E) : outputVariance p (fun _ => w) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOutputVariance`.
--
--   `BookProof.ChapterAttentionOutputVariance.outputVariance_const` (p : Fin m → ℝ) (hp : ∑ j, p j = 1) (w : E) : outputVariance p (fun _ => w) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOutputVariance.outputVariance_const`.

-- Generated from ChapterAttentionOutputVariance.lean — theorem BookProof.ChapterAttentionOutputVariance.outputVariance_const
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionOutputVariance
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableExpectation
open BookProof.ChapterAttentionOutputVariance


open scoped BigOperators RealInnerProductSpace

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BookProof.ChapterAttentionOutputVariance.outputVariance_const (p : Fin m → ℝ) (hp : ∑ j, p j = 1) (w : E) :
    outputVariance p (fun _ => w) = 0 := by sorry
