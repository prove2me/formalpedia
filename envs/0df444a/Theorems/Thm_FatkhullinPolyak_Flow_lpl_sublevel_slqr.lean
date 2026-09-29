-- Prove2me | Theorems.Thm_FatkhullinPolyak_Flow_lpl_sublevel_slqr
-- name    : FatkhullinPolyak.Flow.lpl_sublevel_slqr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:46:17.869025+00:00
-- url     : https://prove2.me/theorems/60acdd43-e7db-4c45-91f2-0daedde6bd85
-- title:
--   Theorem 3.17 — gradient domination (LPL) on $\mathcal S_0$ for state feedback, with $\mu$ of (3.11)
-- statement:
--   Consider state feedback, $C=I$ (so $r=n$), with $B\neq0$, $Q, R, \Sigma\succ0$ and $K_0\in\mathcal S$. Let $K_*\in\mathcal S$ be a minimum point of $f_S$ on $\mathcal S$, and let $\mu$ be the constant (3.11),
--   $$\mu = \frac{\lambda_1(R)\,\lambda_1^2(\Sigma)\,\lambda_1(Q)}{8 f_S(K_*)\Big(\|A\| + \dfrac{\|B\|^2 f_S(K_0)}{\lambda_1(\Sigma)\lambda_1(R)}\Big)^2},$$
--   with $\|\cdot\|$ the spectral norm. Then $\mu>0$ and for every $K\in\mathcal S_0$
--   $$\frac12\,\|\nabla f_S(K)\|_F^2 \;\ge\; \mu\,\big(f_S(K) - f_S(K_*)\big).$$
--
--   This gradient-domination (Łojasiewicz–Polyak) inequality replaces convexity: it turns the decrease of $f$ along the flow into exponential convergence of $f(K_t)$ to the optimal value.
--
--   **Formalization Note** $C=I$ is expressed by a matrix argument $C$ with the hypothesis $C=1$. The optimal gain is a hypothesis ($K_*\in\mathcal S$ and $f(K_*)\le f(K)$ for all $K\in\mathcal S$); its existence is Corollary 3.10. $f(K_*)>0$ is not assumed; it follows from the other hypotheses.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 10, Theorem 3.17, (3.10)–(3.11)

import Mathlib
import Definitions.Def_FatkhullinPolyak_Flow_LQR
import Definitions.Def_FatkhullinPolyak_Flow_LPLConstant

namespace FatkhullinPolyak.Flow

open Matrix

theorem lpl_sublevel_slqr {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C = 1)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hB : B ≠ 0)
    (K₀ : Matrix (Fin m) (Fin n) ℝ) (hK₀ : K₀ ∈ stabSet A B C)
    (Kstar : Matrix (Fin m) (Fin n) ℝ) (hKstar : Kstar ∈ stabSet A B C)
    (hopt : ∀ K ∈ stabSet A B C, cost A B C Q R Sig Kstar ≤ cost A B C Q R Sig K) :
    0 < muLPL A B Q R Sig K₀ Kstar ∧
      ∀ K ∈ sublevel A B C Q R Sig K₀,
        (1 / 2 : ℝ) * frobNorm (grad A B C Q R Sig K) ^ 2 ≥
          muLPL A B Q R Sig K₀ Kstar * (cost A B C Q R Sig K - cost A B C Q R Sig Kstar) := by sorry

end FatkhullinPolyak.Flow
