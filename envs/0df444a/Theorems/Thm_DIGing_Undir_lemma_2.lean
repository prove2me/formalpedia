-- Prove2me | Theorems.Thm_DIGing_Undir_lemma_2
-- name    : DIGing.Undir.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:10:55.544526+00:00
-- url     : https://prove2.me/theorems/67b9629f-3107-492c-9a05-3b2b6ac20404
-- title:
--   Lemma 2, p. 8 — B-step consensus contraction ‖W_B(k)b‖_L ≤ δ(k)‖b‖_L for k ≥ B − 1
-- statement:
--   Let $W(0),W(1),\dots$ be doubly stochastic $n\times n$ matrices (nonnegative entries, unit row and column sums), let $B\ge0$, and let $W_B(k)=W(k)\cdots W(k-B+1)$ and $\delta(k)=\sigma_{\max}\{W_B(k)-\frac1n\mathbf 1\mathbf 1^\top\}$. Then for every $k\ge B-1$ and every $n\times p$ matrix $\mathbf b$, the matrix $\mathbf a=W_B(k)\mathbf b$ satisfies
--   $$\|\mathbf a\|_{\mathbf L}\le\delta(k)\,\|\mathbf b\|_{\mathbf L},$$
--   where $\|\mathbf v\|_{\mathbf L}=\|\mathbf v-\mathbf 1\bar v^\top\|_F$ is the norm of the consensus violation.
--
--   This is the basic consensus estimate of the paper: under Assumption 1(iii) the factor $\delta(k)$ is uniformly below $1$, so $B$ steps of mixing shrink the distance to the consensus subspace by a fixed factor. Lemmas 6 and 7 rest on it.
--
--   **Formalization Note.** Only Assumption 1(ii) is assumed; items (i) and (iii) are not used by the statement and are dropped, which makes it stronger. $\|\cdot\|_{\mathbf L}$ is `frob (cons ·)`; $\delta(k)$ is the operator norm of an $n\times n$ matrix while $\|\cdot\|_{\mathbf L}$ is a norm of $n\times p$ matrices, as on the page.
-- source:
--   Nedić, Olshevsky & Shi, arXiv:1607.03218v3, Lemma 2, p. 8

import Mathlib
import Definitions.Def_DIGing_Undir_Common
import Definitions.Def_DIGing_Undir_Setting

namespace DIGing.Undir

theorem lemma_2 {n p : ℕ} (W : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hW : ∀ k, W k ∈ doublyStochastic ℝ (Fin n)) (B : ℕ) :
    ∀ k : ℕ, B - 1 ≤ k → ∀ b : Stack n p,
      frob (cons (mix (prodW W B k) b)) ≤ deltaK W B k * frob (cons b) := by sorry

end DIGing.Undir
