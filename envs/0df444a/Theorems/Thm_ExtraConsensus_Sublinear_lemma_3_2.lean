-- Prove2me | Theorems.Thm_ExtraConsensus_Sublinear_lemma_3_2
-- name    : ExtraConsensus.Sublinear.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:17.42498+00:00
-- url     : https://prove2.me/theorems/623225da-2b83-48a2-8aa4-dec18300ff5d
-- title:
--   Lemma 3.2, p. 10 — (I + W − 2W̃)(x^{k+1} − x*) + W̃(x^{k+1} − x^k) = −U(q^{k+1} − q*) − α[∇f(x^k) − ∇f(x*)]
-- statement:
--   Assume Assumption 1, let $U=U^{\mathsf T}\succeq0$ with $U^2=\tilde W-W$, let $\alpha\in\mathbb R$, and let $(\mathbf q^*,\mathbf x^*)$ satisfy the optimality conditions (3.1)–(3.2) of Lemma 3.1. Let $\mathbf x^k$ be the EXTRA iterates from any $\mathbf x^0$ and $\mathbf q^k=\sum_{t=0}^kU\mathbf x^t$. Then for every $k=0,1,\dots$
--   $$(I+W-2\tilde W)(\mathbf x^{k+1}-\mathbf x^*)+\tilde W(\mathbf x^{k+1}-\mathbf x^k)=-U(\mathbf q^{k+1}-\mathbf q^*)-\alpha\big[\nabla\mathbf f(\mathbf x^k)-\nabla\mathbf f(\mathbf x^*)\big].\tag{3.4}$$
--
--   Every convergence estimate of the paper starts from this recursion relating the iterates to an optimal pair.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, Lemma 3.2, eq. (3.4), p. 10

import Mathlib
import Definitions.Def_ExtraConsensus_Sublinear_Model

namespace ExtraConsensus.Sublinear

open Matrix Filter Topology Asymptotics

/-- Lemma 3.2, p. 10. Under Assumption 1, with `U` the symmetric positive semidefinite square root
of `W̃ − W`, let `(𝐪*, 𝐱*)` satisfy the optimality conditions (3.1)–(3.2). Then for every `k ≥ 0`
the EXTRA iterates `𝐱ᵏ` and `𝐪ᵏ = Σ_{t≤k} U𝐱ᵗ` obey (3.4):
`(I + W − 2W̃)(𝐱^{k+1} − 𝐱*) + W̃(𝐱^{k+1} − 𝐱ᵏ) = −U(𝐪^{k+1} − 𝐪*) − α[∇𝐟(𝐱ᵏ) − ∇𝐟(𝐱*)]`. -/
theorem lemma_3_2 {n p : ℕ} (Gr : SimpleGraph (Fin n))
    (W Wt U : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (α : ℝ)
    (hA1 : MixingAssumption Gr W Wt)
    (hUs : Uᵀ = U) (hUpsd : U.PosSemidef) (hU2 : U * U = Wt - W)
    (x0 : Stack n p) (qs xs : Stack n p) (hopt : IsOptimalPair U α f qs xs) :
    let x := extraIter α W Wt f x0
    let q := qSeq U x
    ∀ k : ℕ,
      mix (1 + W - (2 : ℝ) • Wt) (x (k + 1) - xs) + mix Wt (x (k + 1) - x k) =
        -(mix U (q (k + 1) - qs)) - α • (gradF f (x k) - gradF f xs) := by sorry

end ExtraConsensus.Sublinear
