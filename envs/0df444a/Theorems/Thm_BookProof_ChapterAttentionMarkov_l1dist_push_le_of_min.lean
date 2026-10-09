-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMarkov_l1dist_push_le_of_min
-- name    : BookProof.ChapterAttentionMarkov.l1dist_push_le_of_min
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:28:20.230581+00:00
-- url     : https://prove2.me/theorems/c70afb54-12e3-405c-9fdb-e92bd6a1cd11
-- title:
--   `BookProof.ChapterAttentionMarkov.l1dist_push_le_of_min` {P : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} {eps : ℝ} (hP : IsStochastic P) (hmin : ∀ i j, eps ≤ P i j) (hp : IsProb p) (hq :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMarkov`.
--
--   `BookProof.ChapterAttentionMarkov.l1dist_push_le_of_min` {P : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} {eps : ℝ} (hP : IsStochastic P) (hmin : ∀ i j, eps ≤ P i j) (hp : IsProb p) (hq : IsProb q) : l1dist (push P p) (push P q) ≤ (1 - m * eps) * l1dist p q
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMarkov.l1dist_push_le_of_min`.

-- Generated from ChapterAttentionMarkov.lean — theorem BookProof.ChapterAttentionMarkov.l1dist_push_le_of_min
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMarkov
import Definitions.Def_ChapterDutchBook
open BookProof.ChapterDutchBook
open BookProof.ChapterAttentionMarkov


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterAttentionMarkov.l1dist_push_le_of_min {P : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} {eps : ℝ}
    (hP : IsStochastic P) (hmin : ∀ i j, eps ≤ P i j) (hp : IsProb p) (hq : IsProb q) :
    l1dist (push P p) (push P q) ≤ (1 - m * eps) * l1dist p q := by sorry
