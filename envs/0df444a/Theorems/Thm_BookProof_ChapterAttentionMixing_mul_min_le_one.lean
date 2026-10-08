-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMixing_mul_min_le_one
-- name    : BookProof.ChapterAttentionMixing.mul_min_le_one
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T13:09:23.177479+00:00
-- url     : https://prove2.me/theorems/a6d977d1-dd91-4674-979a-cb7d6037bdec
-- title:
--   `BookProof.ChapterAttentionMixing.mul_min_le_one` {P : Fin m → Fin m → ℝ} {eps : ℝ} (hP : IsStochastic P) (hmin : ∀ i j, eps ≤ P i j) (i : Fin m) : (m : ℝ) * eps ≤ 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMixing`.
--
--   `BookProof.ChapterAttentionMixing.mul_min_le_one` {P : Fin m → Fin m → ℝ} {eps : ℝ} (hP : IsStochastic P) (hmin : ∀ i j, eps ≤ P i j) (i : Fin m) : (m : ℝ) * eps ≤ 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMixing.mul_min_le_one`.

-- Generated from ChapterAttentionMixing.lean — theorem BookProof.ChapterAttentionMixing.mul_min_le_one
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMixing
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMixing


open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionMarkov

variable {m : ℕ}

theorem BookProof.ChapterAttentionMixing.mul_min_le_one {P : Fin m → Fin m → ℝ} {eps : ℝ} (hP : IsStochastic P)
    (hmin : ∀ i j, eps ≤ P i j) (i : Fin m) : (m : ℝ) * eps ≤ 1 := by sorry
