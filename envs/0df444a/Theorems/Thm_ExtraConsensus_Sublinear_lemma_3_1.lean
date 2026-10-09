-- Prove2me | Theorems.Thm_ExtraConsensus_Sublinear_lemma_3_1
-- name    : ExtraConsensus.Sublinear.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:39.067075+00:00
-- url     : https://prove2.me/theorems/cade46b6-5cce-4721-a865-19e299a8f8d0
-- title:
--   Lemma 3.1, p. 9 — x* is consensual and optimal iff some q* = Up has Uq* + α∇f(x*) = 0 and Ux* = 0
-- statement:
--   Assume Assumptions 1–3, let $\alpha>0$, and let $U$ be the symmetric positive semidefinite square root of $\tilde W-W$, i.e. $U=U^{\mathsf T}\succeq0$ and $U^2=\tilde W-W$. Then for every $\mathbf x^*\in\mathbb R^{n\times p}$: $\mathbf x^*$ is consensual ($x^*_{(1)}=\dots=x^*_{(n)}$) and its common row is optimal for (1.1) if and only if there exists $\mathbf q^*=U\mathbf p$ for some $\mathbf p\in\mathbb R^{n\times p}$ such that
--   $$\begin{cases}U\mathbf q^*+\alpha\nabla\mathbf f(\mathbf x^*)=\mathbf 0, & (3.1)\\ U\mathbf x^*=\mathbf 0. & (3.2)\end{cases}$$
--
--   These first-order optimality conditions define the fixed points $\mathbf z^*=(\mathbf q^*;\mathbf x^*)$ against which the whole convergence analysis is measured.
--
--   **Formalization Note** $U$ is given with the three properties that characterize the paper's $V S^{1/2}V^{\mathsf T}$ (the unique positive semidefinite square root). The hypothesis $\alpha>0$ is the step size of Algorithm 1 and is added explicitly: at $\alpha=0$ condition (3.1) no longer forces optimality.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, Lemma 3.1, p. 9

import Mathlib
import Definitions.Def_ExtraConsensus_Sublinear_Model

namespace ExtraConsensus.Sublinear

open Matrix Filter Topology Asymptotics

/-- Lemma 3.1, p. 9 (first-order optimality conditions). Under Assumptions 1–3, with `U` the
symmetric positive semidefinite square root of `W̃ − W` and step size `α > 0`: `𝐱*` is consensual and
its common row is optimal for (1.1) if and only if there is `𝐪* = U𝐩` with `U𝐪* + α∇𝐟(𝐱*) = 𝟎`
(3.1) and `U𝐱* = 𝟎` (3.2). -/
theorem lemma_3_1 {n p : ℕ} (hn : 0 < n) (Gr : SimpleGraph (Fin n))
    (W Wt U : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (Lf α lmin : ℝ)
    (hA1 : MixingAssumption Gr W Wt) (hA2 : ConvexLipschitzGrad f Lf) (hA3 : SolutionExists f)
    (hUs : Uᵀ = U) (hUpsd : U.PosSemidef) (hU2 : U * U = Wt - W)
    (hα0 : 0 < α) :
    ∀ xs : Stack n p,
      ((∀ i j, xs i = xs j) ∧ ∀ i, ∀ y, fbar f (xs i) ≤ fbar f y) ↔
        ∃ qs : Stack n p, IsOptimalPair U α f qs xs := by sorry

end ExtraConsensus.Sublinear
