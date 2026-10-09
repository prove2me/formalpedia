-- Prove2me | Theorems.Thm_ExtraConsensus_Linear_lemma_3_2
-- name    : ExtraConsensus.Linear.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:16:02.578697+00:00
-- url     : https://prove2.me/theorems/8c2397a5-1f77-44c8-bc83-2d3582b85959
-- title:
--   Lemma 3.2, p. 10 — (I + W − 2W̃)(x^{k+1} − x*) + W̃(x^{k+1} − x^k) = −U(q^{k+1} − q*) − α[∇f(x^k) − ∇f(x*)]
-- statement:
--   Under Assumptions 1–3, let $U$ be the symmetric positive semidefinite square root of $\tilde W-W$, let $(\mathbf q^*,\mathbf x^*)$ satisfy the optimality conditions (3.1)–(3.2) with $\mathbf q^*=U\mathbf p$, let $\mathbf x^k$ be the EXTRA iterates from any $\mathbf x^0$ and $\mathbf q^k=\sum_{t=0}^kU\mathbf x^t$. Then for every $k=0,1,\dots$
--   $$
--   (I+W-2\tilde W)(\mathbf x^{k+1}-\mathbf x^*)+\tilde W(\mathbf x^{k+1}-\mathbf x^k)=-U(\mathbf q^{k+1}-\mathbf q^*)-\alpha\big[\nabla\mathbf f(\mathbf x^k)-\nabla\mathbf f(\mathbf x^*)\big].
--   $$
--   This recursion is the basis of the whole convergence analysis; in the linear-rate proof it is used twice, in (3.24) and in (3.32).
--
--   **Formalization Note** The standing Assumptions 1–3 of §3 are kept as hypotheses, as in the paper; $\mathbf x^*$ is any stacked variable satisfying (3.2), as on the page.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, Lemma 3.2, eq. (3.4), p. 10

import Mathlib
import Definitions.Def_ExtraConsensus_Linear_Model

namespace ExtraConsensus.Linear

open Matrix

/-- Shi–Ling–Wu–Yin, arXiv:1404.6264v4, Lemma 3.2, p. 10 (under the standing Assumptions 1–3 of §3):
for any pair `(𝐪*, 𝐱*)` satisfying the optimality conditions (3.1)–(3.2) with `𝐪* = U𝐩`,
`(I + W − 2W̃)(𝐱^{k+1} − 𝐱*) + W̃(𝐱^{k+1} − 𝐱ᵏ) = −U(𝐪^{k+1} − 𝐪*) − α[∇𝐟(𝐱ᵏ) − ∇𝐟(𝐱*)]`. -/
theorem lemma_3_2 {n p : ℕ} (hn : 0 < n) (Gr : SimpleGraph (Fin n))
    (W Wt U : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lf α : ℝ)
    (hA1 : MixingAssumption Gr W Wt) (hA2 : ExtraConsensus.Sublinear.ConvexLipschitzGrad f Lf) (hA3 : ExtraConsensus.Sublinear.SolutionExists f)
    (hUs : Uᵀ = U) (hUpsd : U.PosSemidef) (hU2 : U * U = Wt - W)
    (qs xs : ExtraConsensus.Sublinear.Stack n p) (hopt : ExtraConsensus.Sublinear.IsOptimalPair U α f qs xs) (x0 : ExtraConsensus.Sublinear.Stack n p) :
    let x := ExtraConsensus.Sublinear.extraIter α W Wt f x0
    let q := ExtraConsensus.Sublinear.qSeq U x
    ∀ k : ℕ, ExtraConsensus.Sublinear.mix (1 + W - (2 : ℝ) • Wt) (x (k + 1) - xs) + ExtraConsensus.Sublinear.mix Wt (x (k + 1) - x k)
      = -(ExtraConsensus.Sublinear.mix U (q (k + 1) - qs)) - α • (ExtraConsensus.Sublinear.gradF f (x k) - ExtraConsensus.Sublinear.gradF f xs) := by sorry

end ExtraConsensus.Linear
