-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOutputVariance_outputVariance_nonneg
-- name    : BookProof.ChapterAttentionOutputVariance.outputVariance_nonneg
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:34:29.205056+00:00
-- url     : https://prove2.me/theorems/fa76be94-affc-473d-953a-19359bcca671
-- title:
--   `BookProof.ChapterAttentionOutputVariance.outputVariance_nonneg` {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (v : Fin m → E) : 0 ≤ outputVariance p v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOutputVariance`.
--
--   `BookProof.ChapterAttentionOutputVariance.outputVariance_nonneg` {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (v : Fin m → E) : 0 ≤ outputVariance p v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOutputVariance.outputVariance_nonneg`.

-- Generated from ChapterAttentionOutputVariance.lean — theorem BookProof.ChapterAttentionOutputVariance.outputVariance_nonneg
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

theorem BookProof.ChapterAttentionOutputVariance.outputVariance_nonneg {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (v : Fin m → E) :
    0 ≤ outputVariance p v := by sorry
