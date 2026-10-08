-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionMixing_eq_of_stationary
-- name    : BookProof.ChapterAttentionMixing.eq_of_stationary
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T13:10:14.156204+00:00
-- url     : https://prove2.me/theorems/cc5e7706-e7c1-46bd-bcca-3919d30d1edd
-- title:
--   `BookProof.ChapterAttentionMixing.eq_of_stationary` {P : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} {eps : ℝ} (hP : IsStochastic P) (hmin : ∀ i j, eps ≤ P i j) (hp : IsProb p) (hq : IsPr
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionMixing`.
--
--   `BookProof.ChapterAttentionMixing.eq_of_stationary` {P : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} {eps : ℝ} (hP : IsStochastic P) (hmin : ∀ i j, eps ≤ P i j) (hp : IsProb p) (hq : IsProb q) (hpos : 0 < eps) (i : Fin m) (hfp : push P p = p) (hfq : push P q = q) : p = q
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionMixing.eq_of_stationary`.

-- Generated from ChapterAttentionMixing.lean — theorem BookProof.ChapterAttentionMixing.eq_of_stationary
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

theorem BookProof.ChapterAttentionMixing.eq_of_stationary {P : Fin m → Fin m → ℝ} {p q : Fin m → ℝ} {eps : ℝ}
    (hP : IsStochastic P) (hmin : ∀ i j, eps ≤ P i j) (hp : IsProb p) (hq : IsProb q)
    (hpos : 0 < eps) (i : Fin m) (hfp : push P p = p) (hfq : push P q = q) : p = q := by sorry
