-- Prove2me | Theorems.Thm_FatkhullinPolyak_Flow_gradient_flow_slqr_exponential
-- name    : FatkhullinPolyak.Flow.gradient_flow_slqr_exponential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:48:31.343453+00:00
-- url     : https://prove2.me/theorems/bfe69ccb-8d03-46d3-8655-d668de74151a
-- title:
--   Theorem 4.1 — the gradient flow for state feedback stays in $\mathcal S_0$ and converges exponentially to the optimal gain
-- statement:
--   Consider state feedback, $C=I$ (so $r=n$), with $B\ne0$, $Q,R,\Sigma\succ0$ and a stabilizing initial gain $K_0\in\mathcal S$. Let $K_*\in\mathcal S$ be a global minimum point of the LQR cost $f=f_S$ on $\mathcal S$. Let $L>0$ be a Lipschitz constant of $\nabla f$ on the sublevel set $\mathcal S_0$:
--   $$\|\nabla f(K)-\nabla f(K')\|_F\le L\|K-K'\|_F\qquad (K,K'\in\mathcal S_0),$$
--   and let $\mu$ be the constant (3.11) of Theorem 3.17. Then the gradient flow (4.1), $\dot K = -\nabla f(K)$, $K(0)=K_0$, has a solution on $[0,\infty)$, and every solution $K_t$ satisfies:
--
--   1. $K_t\in\mathcal S_0$ for all $t\ge0$;
--   2. $t\mapsto f(K_t)$ is nonincreasing on $[0,\infty)$;
--   3. $\|\nabla f(K_t)\|_F\to0$ as $t\to\infty$;
--   4. for every $T>0$, $\displaystyle\min_{0\le t\le T}\|\nabla f(K_t)\|_F^2\le \frac{f(K_0)}{T}$;
--   5. for every $t\ge0$,
--   $$\|K_t - K_*\|_F \le \frac{\sqrt{2L\,(f(K_0)-f(K_*))}}{\mu}\,e^{-\mu t}.$$
--
--   This is Theorem 4.1 of Fatkhullin and Polyak for the state-feedback case: the continuous gradient method started from any stabilizing gain never leaves the sublevel set and converges exponentially fast to the optimal gain, despite the nonconvexity of $f$ and of $\mathcal S$.
--
--   **Formalization Note** The paper takes $L$ from Theorem 3.15, whose explicit value (3.8) is false as printed (see the qualitative Theorem 3.15 of this mission). Here $L$ is any constant for which $\nabla f$ is $L$-Lipschitz on $\mathcal S_0$ in the Frobenius norm, which is the paper's own definition of $L$-smoothness (§3.6, p. 9); such an $L$ exists by the qualitative Theorem 3.15. $C=I$ is expressed by a matrix argument $C$ with $C=1$. The optimal gain is a hypothesis (existence: Corollary 3.10). "Monotone decreasing" is rendered as nonincreasing, and the minimum over $[0,T]$ as the existence of a point where the bound holds. A solution is required to stay in $\mathcal S$; staying in $\mathcal S_0$ and existence for all $t\ge0$ are conclusions. The paper writes both $K_\star$ and $K_*$ for the optimal gain.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 10, Theorem 4.1, (4.2)–(4.3), case C = I

import Mathlib
import Definitions.Def_FatkhullinPolyak_Flow_LQR
import Definitions.Def_FatkhullinPolyak_Flow_GradientFlow
import Definitions.Def_FatkhullinPolyak_Flow_LPLConstant

namespace FatkhullinPolyak.Flow

open Matrix Filter Topology

theorem gradient_flow_slqr_exponential {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C = 1)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hB : B ≠ 0)
    (K₀ : Matrix (Fin m) (Fin n) ℝ) (hK₀ : K₀ ∈ stabSet A B C)
    (Kstar : Matrix (Fin m) (Fin n) ℝ) (hKstar : Kstar ∈ stabSet A B C)
    (hopt : ∀ K ∈ stabSet A B C, cost A B C Q R Sig Kstar ≤ cost A B C Q R Sig K)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ K ∈ sublevel A B C Q R Sig K₀, ∀ K' ∈ sublevel A B C Q R Sig K₀,
      frobNorm (grad A B C Q R Sig K - grad A B C Q R Sig K') ≤ L * frobNorm (K - K')) :
    (∃ K : ℝ → Matrix (Fin m) (Fin n) ℝ, IsGradFlow A B C Q R Sig K₀ K) ∧
      ∀ K : ℝ → Matrix (Fin m) (Fin n) ℝ, IsGradFlow A B C Q R Sig K₀ K →
        (∀ t : ℝ, 0 ≤ t → K t ∈ sublevel A B C Q R Sig K₀) ∧
        AntitoneOn (fun t => cost A B C Q R Sig (K t)) (Set.Ici 0) ∧
        Tendsto (fun t => frobNorm (grad A B C Q R Sig (K t))) atTop (𝓝 0) ∧
        (∀ T : ℝ, 0 < T → ∃ t ∈ Set.Icc (0 : ℝ) T,
          frobNorm (grad A B C Q R Sig (K t)) ^ 2 ≤ cost A B C Q R Sig K₀ / T) ∧
        ∀ t : ℝ, 0 ≤ t →
          frobNorm (K t - Kstar) ≤
            Real.sqrt (2 * L * (cost A B C Q R Sig K₀ - cost A B C Q R Sig Kstar)) /
                muLPL A B Q R Sig K₀ Kstar *
              Real.exp (-(muLPL A B Q R Sig K₀ Kstar) * t) := by sorry

end FatkhullinPolyak.Flow
