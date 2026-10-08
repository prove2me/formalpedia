-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionLocality_scoreSoftmax_alibi_antitone
-- name    : BookProof.ChapterAttentionLocality.scoreSoftmax_alibi_antitone
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:24:37.551281+00:00
-- url     : https://prove2.me/theorems/aa9cca1c-f16a-44db-abf3-5416038e833c
-- title:
--   `BookProof.ChapterAttentionLocality.scoreSoftmax_alibi_antitone` {beta gamma : ℝ} (hb : 0 ≤ beta) (hg : 0 ≤ gamma) (c : ℝ) (d : Fin m → ℝ) {i j : Fin m} (hij : d i ≤ d j) : scoreSo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionLocality`.
--
--   `BookProof.ChapterAttentionLocality.scoreSoftmax_alibi_antitone` {beta gamma : ℝ} (hb : 0 ≤ beta) (hg : 0 ≤ gamma) (c : ℝ) (d : Fin m → ℝ) {i j : Fin m} (hij : d i ≤ d j) : scoreSoftmax beta (alibiScore (fun _ => c) gamma d) j ≤ scoreSoftmax beta (alibiScore (fun _ => c) gamma d) i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionLocality.scoreSoftmax_alibi_antitone`.

-- Generated from ChapterAttentionLocality.lean — theorem BookProof.ChapterAttentionLocality.scoreSoftmax_alibi_antitone
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionLocality
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionLocality


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionLocality.scoreSoftmax_alibi_antitone {beta gamma : ℝ} (hb : 0 ≤ beta) (hg : 0 ≤ gamma)
    (c : ℝ) (d : Fin m → ℝ) {i j : Fin m} (hij : d i ≤ d j) :
    scoreSoftmax beta (alibiScore (fun _ => c) gamma d) j
      ≤ scoreSoftmax beta (alibiScore (fun _ => c) gamma d) i := by sorry
