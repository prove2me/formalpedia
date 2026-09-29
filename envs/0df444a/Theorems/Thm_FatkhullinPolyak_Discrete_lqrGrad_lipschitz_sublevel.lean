-- Prove2me | Theorems.Thm_FatkhullinPolyak_Discrete_lqrGrad_lipschitz_sublevel
-- name    : FatkhullinPolyak.Discrete.lqrGrad_lipschitz_sublevel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:39:41.493396+00:00
-- url     : https://prove2.me/theorems/10c09b1d-95a4-4404-98bc-05d0fd143ab6
-- title:
--   Theorem 3.15 (qualitative form) — the LQR cost is $L$-smooth on $\mathcal S_0$ for some $L>0$
-- statement:
--   Under the standing assumptions ($Q,R,\Sigma\succ0$, $\operatorname{rank}C=r$, $B\ne0$) and for every $K_0\in\mathcal S$, there is a constant $L>0$ such that the gradient (3.3) is $L$-Lipschitz on the sublevel set $\mathcal S_0$ in the Frobenius norm:
--   $$\|\nabla f(K)-\nabla f(K')\|_F\le L\,\|K-K'\|_F\qquad\text{for all }K,K'\in\mathcal S_0 .$$
--
--   This is the $L$-smoothness of §3.6, the only property of $f$ the convergence proof of the gradient method uses. It shows that the hypothesis "$\nabla f$ is $L$-Lipschitz on $\mathcal S_0$" of Theorem 4.2 can be met.
--
--   **Formalization Note** The paper's Theorem 3.15 asserts $L$-smoothness with the explicit constant (3.8). That constant is false as printed: for state feedback with $n=m=1$, $A=0$, $B=100$, $Q=100$, $R=10^{-3}$, $\Sigma=0.1$, $K_0=10^{-6}$ one has $f''(K_0)=10^{17}$, twice the value of (3.8). One cause is the Hessian bound (3.7), which drops the factor 2 of (3.6). Only the existence of a Lipschitz constant is stated here. The paper notes that $f$ is not $L$-smooth on all of $\mathcal S$, so the statement is restricted to $\mathcal S_0$.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 9, §3.6 and Theorem 3.15 (qualitative form; the explicit (3.8) is not claimed)

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

/-- Theorem 3.15, qualitative form (p. 9): on `S₀` the gradient (3.3) is Lipschitz in the
Frobenius norm for some constant `L > 0`, i.e. `f` is `L`-smooth on `S₀`. The explicit constant
(3.8) is not claimed (it is false as printed). -/
theorem lqrGrad_lipschitz_sublevel {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r) (hB : B ≠ 0)
    (K₀ : Matrix (Fin m) (Fin r) ℝ) (hK₀ : K₀ ∈ stabSet A B C) :
    ∃ L : ℝ, 0 < L ∧ ∀ K ∈ sublevel A B C Q R Sig K₀, ∀ K' ∈ sublevel A B C Q R Sig K₀,
      frobNorm (lqrGrad A B C Q R Sig K - lqrGrad A B C Q R Sig K') ≤ L * frobNorm (K - K') := by sorry

end FatkhullinPolyak.Discrete
