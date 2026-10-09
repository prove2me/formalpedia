-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSink_shannonEntropy_cons_scaled
-- name    : BookProof.ChapterAttentionSink.shannonEntropy_cons_scaled
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:48:40.751551+00:00
-- url     : https://prove2.me/theorems/4f00cf5b-4f65-4e43-84b4-89ecbeecd0c1
-- title:
--   `BookProof.ChapterAttentionSink.shannonEntropy_cons_scaled` {w : ℝ} (hw1 : w < 1) {p : Fin m → ℝ} (hp : ∀ j, 0 < p j) (hsum : ∑ j, p j = 1) : shannonEntropy (Fin.cons w (fun j => (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSink`.
--
--   `BookProof.ChapterAttentionSink.shannonEntropy_cons_scaled` {w : ℝ} (hw1 : w < 1) {p : Fin m → ℝ} (hp : ∀ j, 0 < p j) (hsum : ∑ j, p j = 1) : shannonEntropy (Fin.cons w (fun j => (1 - w) * p j) : Fin (m + 1) → ℝ) = (-w * Real.log w - (1 - w) * Real.log (1 - w)) + (1 - w) * shannonEntropy p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSink.shannonEntropy_cons_scaled`.

-- Generated from ChapterAttentionSink.lean — theorem BookProof.ChapterAttentionSink.shannonEntropy_cons_scaled
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionSink
import Definitions.Def_ChapterAttentionEntropy
open BookProof.ChapterAttentionSink


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionEntropy

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionSink.shannonEntropy_cons_scaled {w : ℝ} (hw1 : w < 1) {p : Fin m → ℝ}
    (hp : ∀ j, 0 < p j) (hsum : ∑ j, p j = 1) :
    shannonEntropy (Fin.cons w (fun j => (1 - w) * p j) : Fin (m + 1) → ℝ)
      = (-w * Real.log w - (1 - w) * Real.log (1 - w)) + (1 - w) * shannonEntropy p := by sorry
