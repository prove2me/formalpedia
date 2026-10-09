-- Prove2me | Theorems.Thm_ExtraConsensus_Sublinear_eq_3_5
-- name    : ExtraConsensus.Sublinear.eq_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:52.724441+00:00
-- url     : https://prove2.me/theorems/b49e4e15-fca0-4262-a2c7-6e927c035c31
-- title:
--   Eq. (3.5), p. 10 — summed EXTRA: x^{k+1} = W̃x^k − Σ_{t≤k}(W̃ − W)x^t − α∇f(x^k)
-- statement:
--   Let $\mathbf x^k$ be the EXTRA iterates for any step size $\alpha$, any mixing matrices $W,\tilde W$, any functions $f_i$ ($\nabla$ denotes the gradient) and any start $\mathbf x^0$. Summing the iterations 1 through $k+1$ gives, for every $k\ge0$,
--   $$\mathbf x^{k+1}=\tilde W\mathbf x^k-\sum_{t=0}^{k}(\tilde W-W)\mathbf x^t-\alpha\nabla\mathbf f(\mathbf x^k).$$
--
--   This rewrites the two-step recursion of EXTRA as a one-step update with a cumulative correction term, the form on which Lemma 3.2 rests.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, §3.1, proof of Lemma 3.2, eq. (3.5), p. 10

import Mathlib
import Definitions.Def_ExtraConsensus_Sublinear_Model

namespace ExtraConsensus.Sublinear

open Matrix Filter Topology Asymptotics

/-- Eq. (3.5), p. 10. Summing the EXTRA iterations: for every `k`,
`𝐱^{k+1} = W̃𝐱ᵏ − Σ_{t=0}^{k} (W̃ − W)𝐱ᵗ − α∇𝐟(𝐱ᵏ)`, where `𝐱 = extraIter α W W̃ f 𝐱⁰`. -/
theorem eq_3_5 {n p : ℕ} (W Wt : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (α : ℝ) (x0 : Stack n p) :
    let x := extraIter α W Wt f x0
    ∀ k : ℕ, x (k + 1) =
      mix Wt (x k) - ∑ t ∈ Finset.range (k + 1), mix (Wt - W) (x t) - α • gradF f (x k) := by sorry

end ExtraConsensus.Sublinear
