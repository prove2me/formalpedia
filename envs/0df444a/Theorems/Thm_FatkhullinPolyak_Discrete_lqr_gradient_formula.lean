-- Prove2me | Theorems.Thm_FatkhullinPolyak_Discrete_lqr_gradient_formula
-- name    : FatkhullinPolyak.Discrete.lqr_gradient_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:38:49.735871+00:00
-- url     : https://prove2.me/theorems/3290cdf5-4342-4d85-a4b5-cd4e6bff8e44
-- title:
--   Lemma 3.11 — the gradient of the LQR cost is $2(RKC-B^\top X)YC^\top$
-- statement:
--   Under the standing assumptions, for every $K\in\mathcal S$ the cost $f$ is (Fréchet) differentiable at $K$ with gradient, with respect to the Frobenius inner product $\langle M,N\rangle=\mathrm{Tr}(M^\top N)$,
--   $$\nabla f(K)=2\big(RKC-B^\top X\big)\,Y\,C^\top, \tag{3.3}$$
--   where $X=X(K)$ solves (2.7) and $Y$ solves the Lyapunov equation
--   $$A_KY+YA_K^\top+\Sigma=0. \tag{3.4}$$
--   That is, for every $\varepsilon>0$ there is $\delta>0$ such that
--   $$\big|f(K+E)-f(K)-\langle\nabla f(K),E\rangle\big|\le\varepsilon\|E\|_F\qquad\text{whenever }\|E\|_F<\delta .$$
--
--   The explicit gradient is what the gradient method (4.4) evaluates at each step.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 7, Lemma 3.11, (3.3)–(3.4)

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

/-- Lemma 3.11 (p. 7): for every `K ∈ S`, `f` is Fréchet differentiable at `K` (Frobenius norm)
with gradient `∇f(K) = 2(RKC − BᵀX)YCᵀ` of (3.3), `Y` the solution of (3.4); i.e.
`f(K + E) = f(K) + ⟨∇f(K), E⟩_F + o(‖E‖_F)`. -/
theorem lqr_gradient_formula {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r) (hB : B ≠ 0)
    (K : Matrix (Fin m) (Fin r) ℝ) (hK : K ∈ stabSet A B C) :
    ∀ ε > 0, ∃ δ > 0, ∀ E : Matrix (Fin m) (Fin r) ℝ, frobNorm E < δ →
      |lqrCost A B C Q R Sig (K + E) - lqrCost A B C Q R Sig K
          - frobInner (lqrGrad A B C Q R Sig K) E| ≤ ε * frobNorm E := by sorry

end FatkhullinPolyak.Discrete
