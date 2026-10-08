-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCapacity_scoreSoftmax_distScore_ge_of_separated
-- name    : BookProof.ChapterAttentionCapacity.scoreSoftmax_distScore_ge_of_separated
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:53:30.707993+00:00
-- url     : https://prove2.me/theorems/014b513b-783b-4252-a26d-c869fc7d9574
-- title:
--   `BookProof.ChapterAttentionCapacity.scoreSoftmax_distScore_ge_of_separated` {k : Fin m → EuclideanSpace ℝ (Fin n)} {r beta : ℝ} (hb : 0 ≤ beta) (hr : 0 ≤ r) (hsep : keysSeparated k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCapacity`.
--
--   `BookProof.ChapterAttentionCapacity.scoreSoftmax_distScore_ge_of_separated` {k : Fin m → EuclideanSpace ℝ (Fin n)} {r beta : ℝ} (hb : 0 ≤ beta) (hr : 0 ≤ r) (hsep : keysSeparated k r) (i : Fin m) : 1 / (1 + ((m : ℝ) - 1) * Real.exp (-(beta * r ^ 2))) ≤ scoreSoftmax beta (distScore (k i) k) i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCapacity.scoreSoftmax_distScore_ge_of_separated`.

-- Generated from ChapterAttentionCapacity.lean — theorem BookProof.ChapterAttentionCapacity.scoreSoftmax_distScore_ge_of_separated
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionCapacity
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionCapacity


open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionCapacity.scoreSoftmax_distScore_ge_of_separated {k : Fin m → EuclideanSpace ℝ (Fin n)}
    {r beta : ℝ} (hb : 0 ≤ beta) (hr : 0 ≤ r) (hsep : keysSeparated k r) (i : Fin m) :
    1 / (1 + ((m : ℝ) - 1) * Real.exp (-(beta * r ^ 2)))
      ≤ scoreSoftmax beta (distScore (k i) k) i := by sorry
