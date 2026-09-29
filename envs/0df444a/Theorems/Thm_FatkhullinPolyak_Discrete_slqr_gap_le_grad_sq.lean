-- Prove2me | Theorems.Thm_FatkhullinPolyak_Discrete_slqr_gap_le_grad_sq
-- name    : FatkhullinPolyak.Discrete.slqr_gap_le_grad_sq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:41:13.696627+00:00
-- url     : https://prove2.me/theorems/8a7f2ecf-0204-45f9-9cc1-0e55955d9428
-- title:
--   Lemma C.1 — for state feedback, $f_S(K)-f_S(K_*)\le\frac{(\|A\|+\|K\|_F\|B\|)^2\lambda_n(Y_*)}{\lambda_1(R)\lambda_1^2(\Sigma)}\|\nabla f_S(K)\|_F^2$ on $\mathcal S_0$
-- statement:
--   Consider state feedback, $C=I$, with $Q,R,\Sigma\succ0$ and $B\ne0$. Let $K_*\in\mathcal S$ be an optimal gain ($f_S(K_*)\le f_S(K)$ for all $K\in\mathcal S$), let $K_0\in\mathcal S$, and let $Y_*$ solve
--   $$A_{K_*}Y_*+Y_*A_{K_*}^\top+\Sigma=0. \tag{C.2}$$
--   Then for every $K\in\mathcal S_0$,
--   $$f_S(K)-f_S(K_*)\le\frac{\big(\|A\|+\|K\|_F\|B\|\big)^2\,\lambda_n(Y_*)}{\lambda_1(R)\,\lambda_1^2(\Sigma)}\,\|\nabla f_S(K)\|_F^2, \tag{C.1}$$
--   where $\|\cdot\|$ is the spectral norm.
--
--   This is the gradient-domination inequality with a $K$-dependent constant; bounding $\|K\|_F$ by Lemma C.3 and $\lambda_n(Y_*)$ by Lemma C.2 turns it into the LPL condition of Theorem 3.17.
--
--   **Formalization Note** The statement on p. 17 prints $\lambda_1(R)\lambda_1(\Sigma)$ in the denominator. The proof on p. 18 ends with $\lambda_1(R)\lambda_1^2(\Sigma)$, and the constant $\mu$ of (3.11) is computed from that. The printed version is false when $\lambda_1(\Sigma)<1$ (the ratio reaches about $1000$ at $\lambda_1(\Sigma)=10^{-3}$), so the proved form with $\lambda_1^2(\Sigma)$ is stated.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 17, Lemma C.1, (C.1)–(C.2) (denominator λ₁²(Σ) as concluded in the proof, p. 18)

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

/-- Lemma C.1 (p. 17), state feedback `C = I`, with the misprint `λ₁(Σ)` corrected to `λ₁²(Σ)`
(as the proof on p. 18 concludes): for an optimal `K⋆ ∈ S`, `K₀ ∈ S` and `K ∈ S₀`,
(C.1) `f(K) − f(K⋆) ≤ (‖A‖ + ‖K‖_F‖B‖)² λₙ(Y⋆) / (λ₁(R)λ₁²(Σ)) · ‖∇f(K)‖_F²`,
`Y⋆` the solution of (C.2) `A_{K⋆} Y⋆ + Y⋆ A_{K⋆}ᵀ + Σ = 0`. -/
theorem slqr_gap_le_grad_sq {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hB : B ≠ 0)
    (K₀ Kstar K : Matrix (Fin m) (Fin n) ℝ) (hK₀ : K₀ ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ))
    (hKstar : Kstar ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ))
    (hopt : ∀ K' ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ), lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig Kstar ≤ lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K')
    (hK : K ∈ sublevel A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀) :
    lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K - lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig Kstar ≤
      (specNorm A + frobNorm K * specNorm B) ^ 2 * lamMax (lyapY A B (1 : Matrix (Fin n) (Fin n) ℝ) Sig Kstar)
        / (lamMin R * lamMin Sig ^ 2) * frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K) ^ 2 := by sorry

end FatkhullinPolyak.Discrete
