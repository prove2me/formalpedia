-- Prove2me | Theorems.Thm_FatkhullinPolyak_Flow_grad_lipschitz_on_sublevel
-- name    : FatkhullinPolyak.Flow.grad_lipschitz_on_sublevel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:45:45.437687+00:00
-- url     : https://prove2.me/theorems/2407414f-b847-4e86-aeda-0bec5a95fb70
-- title:
--   Theorem 3.15 (qualitative form) — $\nabla f$ is Lipschitz on the sublevel set $\mathcal S_0$
-- statement:
--   Assume the standing assumptions: $B\ne0$, $\operatorname{rank}C=r$, $Q, R, \Sigma\succ0$, and $K_0\in\mathcal S$. Then $f$ is $L$-smooth on the sublevel set $\mathcal S_0=\{K\in\mathcal S: f(K)\le f(K_0)\}$ for some constant $L$: there is $L>0$ with
--   $$\|\nabla f(K) - \nabla f(K')\|_F \le L\,\|K-K'\|_F\qquad\text{for all } K, K'\in\mathcal S_0 .$$
--
--   This is the property the paper calls $L$-smoothness (§3.6, p. 9: "a function is called $L$-smooth, if its gradient satisfies Lipschitz condition with constant $L$"). It shows that the Lipschitz hypothesis of the main theorem can always be met.
--
--   **Formalization Note** The paper's Theorem 3.15 also gives an explicit value (3.8) for $L$. That value is not claimed here, because it is false as printed: for $n=m=r=1$, $A=0$, $B=\tfrac12$, $C=10$, $Q=R=\Sigma=1$, $K_0=0.2$ one has $f''=1600$ on $\mathcal S_0$ while (3.8) gives $L\approx678.2$; for state feedback with $A=0$, $B=100$, $Q=100$, $R=10^{-3}$, $\Sigma=0.1$, $K_0=10^{-6}$, $f''(K_0)$ is twice the value of (3.8). Only the existence of a Lipschitz constant is stated.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 9, §3.6 and Theorem 3.15 (qualitative form; the explicit constant (3.8) is not stated)

import Mathlib
import Definitions.Def_FatkhullinPolyak_Flow_LQR

namespace FatkhullinPolyak.Flow

open Matrix

theorem grad_lipschitz_on_sublevel {n m r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (C : Matrix (Fin r) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r) (hB : B ≠ 0)
    (K₀ : Matrix (Fin m) (Fin r) ℝ) (hK₀ : K₀ ∈ stabSet A B C) :
    ∃ L : ℝ, 0 < L ∧
      ∀ K ∈ sublevel A B C Q R Sig K₀, ∀ K' ∈ sublevel A B C Q R Sig K₀,
        frobNorm (grad A B C Q R Sig K - grad A B C Q R Sig K') ≤ L * frobNorm (K - K') := by sorry

end FatkhullinPolyak.Flow
