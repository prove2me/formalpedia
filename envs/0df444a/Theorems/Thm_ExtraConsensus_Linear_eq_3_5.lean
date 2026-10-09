-- Prove2me | Theorems.Thm_ExtraConsensus_Linear_eq_3_5
-- name    : ExtraConsensus.Linear.eq_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:16:15.916102+00:00
-- url     : https://prove2.me/theorems/038fba98-0a08-453e-967c-7e51707d68c9
-- title:
--   Eq. (3.5), p. 10 — summed EXTRA: x^{k+1} = W̃x^k − Σ_{t≤k}(W̃ − W)x^t − α∇f(x^k)
-- statement:
--   Let $W,\tilde W$ be $n\times n$ matrices, $\alpha\in\mathbb R$, and let $\mathbf x^0,\mathbf x^1,\dots$ be the EXTRA iterates started at any $\mathbf x^0\in\mathbb R^{n\times p}$. Summing the EXTRA iterations $1$ through $k+1$ gives, for every $k\ge0$,
--   $$
--   \mathbf x^{k+1}=\tilde W\mathbf x^k-\sum_{t=0}^{k}(\tilde W-W)\mathbf x^t-\alpha\nabla\mathbf f(\mathbf x^k).
--   $$
--   This summed form expresses EXTRA as a gradient step corrected by the accumulated consensus error $\sum_t(\tilde W-W)\mathbf x^t$; it is the starting point of Lemma 3.2.
--
--   **Formalization Note** The identity is purely algebraic and holds for every $W,\tilde W,\alpha$ and every $f_i$, so no assumption is stated.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, proof of Lemma 3.2, eq. (3.5), p. 10

import Mathlib
import Definitions.Def_ExtraConsensus_Linear_Model

namespace ExtraConsensus.Linear

open Matrix

/-- Shi–Ling–Wu–Yin, arXiv:1404.6264v4, eq. (3.5), p. 10: summing EXTRA's iterations,
`𝐱^{k+1} = W̃𝐱ᵏ − ∑_{t=0}^{k} (W̃ − W)𝐱ᵗ − α∇𝐟(𝐱ᵏ)` for every `k`. -/
theorem eq_3_5 {n p : ℕ} (W Wt : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (α : ℝ) (x0 : ExtraConsensus.Sublinear.Stack n p) :
    let x := ExtraConsensus.Sublinear.extraIter α W Wt f x0
    ∀ k : ℕ, x (k + 1) = ExtraConsensus.Sublinear.mix Wt (x k) - ∑ t ∈ Finset.range (k + 1), ExtraConsensus.Sublinear.mix (Wt - W) (x t)
      - α • ExtraConsensus.Sublinear.gradF f (x k) := by sorry

end ExtraConsensus.Linear
