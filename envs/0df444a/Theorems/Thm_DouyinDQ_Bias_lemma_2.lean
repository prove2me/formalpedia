-- Prove2me | Theorems.Thm_DouyinDQ_Bias_lemma_2
-- name    : DouyinDQ.Bias.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:14.229669+00:00
-- url     : https://prove2.me/theorems/1654661b-4d81-432f-ac35-a9e4a9d45161
-- title:
--   Lemma 2, p. 9 — finite resolvent expansion with exact remainder
-- statement:
--   Let $A,A'$ be real square matrices with both $I-A$ and $I-A'$ invertible. For every integer $K\ge0$, the inverse of $I-A'$ is the sum of the first $K+1$ terms of its resolvent expansion around $A$, plus an exact remainder:
--   $$
--   (I-A')^{-1}=(I-A)^{-1}\sum_{k=0}^{K}[(A'-A)(I-A)^{-1}]^k+(I-A')^{-1}[(A'-A)(I-A)^{-1}]^{K+1}.
--   $$
--   The identity supplies the finite-order expansion used in the paper's value-functional theorem.
-- source:
--   Farias, Li, Peng, Ren, Zhang, Zheng, Correcting for Interference in Experiments: A Case Study at Douyin, arXiv:2305.02542v1, p. 9, Lemma 2

import Mathlib

namespace DouyinDQ.Bias

/-- Lemma 2, p. 9: finite resolvent expansion with its exact remainder. -/
theorem lemma_2 {ι : Type} [Fintype ι] [DecidableEq ι]
    (A A' : Matrix ι ι ℝ)
    (hA : IsUnit (1 - A).det) (hA' : IsUnit (1 - A').det) (K : ℕ) :
    (1 - A')⁻¹ = (1 - A)⁻¹ *
      (∑ k ∈ Finset.range (K + 1), ((A' - A) * (1 - A)⁻¹) ^ k) +
      (1 - A')⁻¹ * ((A' - A) * (1 - A)⁻¹) ^ (K + 1) := by sorry

end DouyinDQ.Bias
