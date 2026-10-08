-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMixing_pushIter_isProb
-- name    : BookProof.ChapterAttentionMixing.pushIter_isProb
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T13:08:16.358037+00:00
-- url     : https://prove2.me/theorems/ac8e2446-ebca-46cc-9b6a-cf8c71a06638
-- title:
--   `BookProof.ChapterAttentionMixing.pushIter_isProb` {P : Fin m → Fin m → ℝ} {p : Fin m → ℝ} (hP : IsStochastic P) (hp : IsProb p) (n : ℕ) : IsProb (pushIter P n p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMixing`.
--
--   `BookProof.ChapterAttentionMixing.pushIter_isProb` {P : Fin m → Fin m → ℝ} {p : Fin m → ℝ} (hP : IsStochastic P) (hp : IsProb p) (n : ℕ) : IsProb (pushIter P n p)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMixing.pushIter_isProb`.

-- Generated from ChapterAttentionMixing.lean — theorem BookProof.ChapterAttentionMixing.pushIter_isProb
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionMixing
import Definitions.Def_ChapterDutchBook
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMixing


open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterAttentionMarkov

variable {m : ℕ}

theorem BookProof.ChapterAttentionMixing.pushIter_isProb {P : Fin m → Fin m → ℝ} {p : Fin m → ℝ} (hP : IsStochastic P)
    (hp : IsProb p) (n : ℕ) : IsProb (pushIter P n p) := by sorry
