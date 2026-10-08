-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionSink_shannonEntropy_sink
-- name    : BookProof.ChapterAttentionSink.shannonEntropy_sink
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:48:35.398441+00:00
-- url     : https://prove2.me/theorems/0bbe9908-f1e9-428f-8533-5064eff1c219
-- title:
--   `BookProof.ChapterAttentionSink.shannonEntropy_sink` (beta s0 : ℝ) (s : Fin m → ℝ) (i : Fin m) : shannonEntropy (scoreSoftmax beta (Fin.cons s0 s)) = (-sinkWeight beta s0 s * Real.
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionSink`.
--
--   `BookProof.ChapterAttentionSink.shannonEntropy_sink` (beta s0 : ℝ) (s : Fin m → ℝ) (i : Fin m) : shannonEntropy (scoreSoftmax beta (Fin.cons s0 s)) = (-sinkWeight beta s0 s * Real.log (sinkWeight beta s0 s) - (1 - sinkWeight beta s0 s) * Real.log (1 - sinkWeight beta s0 s)) + (1 - sinkWeight beta s0 s) * shannonEntropy (scoreSoftmax beta s)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionSink.shannonEntropy_sink`.

-- Generated from ChapterAttentionSink.lean — theorem BookProof.ChapterAttentionSink.shannonEntropy_sink
import Definitions.Def_ChapterObservableExpectation
import Mathlib
import Definitions.Def_ChapterAttentionSink
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionEntropy
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionSink


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionEntropy

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionSink.shannonEntropy_sink (beta s0 : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    shannonEntropy (scoreSoftmax beta (Fin.cons s0 s))
      = (-sinkWeight beta s0 s * Real.log (sinkWeight beta s0 s)
          - (1 - sinkWeight beta s0 s) * Real.log (1 - sinkWeight beta s0 s))
        + (1 - sinkWeight beta s0 s) * shannonEntropy (scoreSoftmax beta s) := by sorry
