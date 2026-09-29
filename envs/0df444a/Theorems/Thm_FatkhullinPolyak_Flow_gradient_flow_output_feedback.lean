-- Prove2me | Theorems.Thm_FatkhullinPolyak_Flow_gradient_flow_output_feedback
-- name    : FatkhullinPolyak.Flow.gradient_flow_output_feedback
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:47:51.095282+00:00
-- url     : https://prove2.me/theorems/5e3f53c5-0e5e-4bc5-b620-d7202dac4599
-- title:
--   Theorem 4.1 (output feedback: the flow stays in $\mathcal S_0$ and $\nabla f\to0$)
-- statement:
--   Assume the standing assumptions: $B\ne0$, $\operatorname{rank}C = r$, $Q,R,\Sigma\succ0$, and $K_0\in\mathcal S$. Then the gradient flow (4.1), $\dot K = -\nabla f(K)$, $K(0)=K_0$, has a solution on $[0,\infty)$, and every solution $K_t$ satisfies:
--
--   1. $K_t\in\mathcal S_0$ for all $t\ge0$;
--   2. $t\mapsto f(K_t)$ is nonincreasing on $[0,\infty)$;
--   3. $\|\nabla f(K_t)\|_F\to0$ as $t\to\infty$;
--   4. for every $T>0$,
--   $$\min_{0\le t\le T}\|\nabla f(K_t)\|_F^2 \le \frac{f(K_0)}{T}.$$
--
--   This is the first sentence of Theorem 4.1, which holds for output feedback (general $C$); convergence to a stationary point is all the paper claims in that case.
--
--   **Formalization Note** "Monotone decreasing" is rendered as nonincreasing (the flow is stationary once it reaches a critical point). The minimum over $[0,T]$ is rendered as the existence of $t\in[0,T]$ satisfying the bound. A solution is required to stay in $\mathcal S$ (where $\nabla f$ is meaningful); staying in $\mathcal S_0$ and existence for all $t\ge0$ are conclusions. $\|\cdot\|$ in (4.2) is the Frobenius norm.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 10, Theorem 4.1, first sentence and (4.2)

import Mathlib
import Definitions.Def_FatkhullinPolyak_Flow_LQR
import Definitions.Def_FatkhullinPolyak_Flow_GradientFlow

namespace FatkhullinPolyak.Flow

open Matrix Filter Topology

theorem gradient_flow_output_feedback {n m r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin r) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r) (hB : B ≠ 0)
    (K₀ : Matrix (Fin m) (Fin r) ℝ) (hK₀ : K₀ ∈ stabSet A B C) :
    (∃ K : ℝ → Matrix (Fin m) (Fin r) ℝ, IsGradFlow A B C Q R Sig K₀ K) ∧
      ∀ K : ℝ → Matrix (Fin m) (Fin r) ℝ, IsGradFlow A B C Q R Sig K₀ K →
        (∀ t : ℝ, 0 ≤ t → K t ∈ sublevel A B C Q R Sig K₀) ∧
        AntitoneOn (fun t => cost A B C Q R Sig (K t)) (Set.Ici 0) ∧
        Tendsto (fun t => frobNorm (grad A B C Q R Sig (K t))) atTop (𝓝 0) ∧
        ∀ T : ℝ, 0 < T → ∃ t ∈ Set.Icc (0 : ℝ) T,
          frobNorm (grad A B C Q R Sig (K t)) ^ 2 ≤ cost A B C Q R Sig K₀ / T := by sorry

end FatkhullinPolyak.Flow
