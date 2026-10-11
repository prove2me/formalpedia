-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxOrder_softmax_le_iff_inner_le
-- name    : BookProof.ChapterSoftmaxOrder.softmax_le_iff_inner_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:36:53.480514+00:00
-- url     : https://prove2.me/theorems/d07c7361-3301-43e8-b8a7-0e4c967478d1
-- title:
--   `BookProof.ChapterSoftmaxOrder.softmax_le_iff_inner_le` {n : ℕ} {beta : ℝ} (hbeta : 0 < beta) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (i j : Fin m) :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxOrder`.
--
--   `BookProof.ChapterSoftmaxOrder.softmax_le_iff_inner_le` {n : ℕ} {beta : ℝ} (hbeta : 0 < beta) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (i j : Fin m) : softmax beta q k i ≤ softmax beta q k j ↔ (inner ℝ q (k i) : ℝ) ≤ inner ℝ q (k j)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxOrder.softmax_le_iff_inner_le`.

-- Generated from ChapterSoftmaxOrder.lean — theorem BookProof.ChapterSoftmaxOrder.softmax_le_iff_inner_le
import Mathlib
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxOrder


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxOrder.softmax_le_iff_inner_le {n : ℕ} {beta : ℝ} (hbeta : 0 < beta)
    (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (i j : Fin m) :
    softmax beta q k i ≤ softmax beta q k j ↔
      (inner ℝ q (k i) : ℝ) ≤ inner ℝ q (k j) := by sorry
