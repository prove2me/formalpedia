-- Prove2me | Theorems.Thm_FatkhullinPolyak_Discrete_gradient_method_slqr_linear_rate
-- name    : FatkhullinPolyak.Discrete.gradient_method_slqr_linear_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:42:36.103416+00:00
-- url     : https://prove2.me/theorems/81ee943d-a1dc-4f7a-8813-8a2cfd12f9c6
-- title:
--   Theorem 4.2 for state feedback — the gradient method stays in $\mathcal S_0$, reaches stationarity, and converges linearly to the optimal gain
-- statement:
--   Consider state feedback, $C=I$ (so $r=n$), with $Q,R,\Sigma\succ0$, $B\ne0$ and a stabilizing gain $K_0\in\mathcal S$. Let $K_*\in\mathcal S$ be an optimal gain, $f(K_*)\le f(K)$ for all $K\in\mathcal S$. Let $L>0$ be a Lipschitz constant of the gradient (3.3) on $\mathcal S_0$:
--   $$\|\nabla f(K)-\nabla f(K')\|_F\le L\|K-K'\|_F\qquad(K,K'\in\mathcal S_0).$$
--   Let $(\gamma_j)$ be real step sizes and $K_{j+1}=K_j-\gamma_j\nabla f(K_j)$ the gradient method (4.4) from $K_0$.
--
--   1. If $0<\gamma_j\le2/L$ for all $j$, then every $K_j$ lies in $\mathcal S_0$ and
--   $$f(K_{j+1})\le f(K_j)-\gamma_j\Big(1-\frac{L\gamma_j}{2}\Big)\|\nabla f(K_j)\|_F^2\qquad\text{for all }j. \tag{4.5}$$
--   2. If $0<\varepsilon_1\le\gamma_j\le2/L-\varepsilon_2$ for all $j$, with $\varepsilon_2>0$, then $\nabla f(K_j)\to0$,
--   $$\min_{0\le j\le k}\|\nabla f(K_j)\|_F^2\le\frac{f(K_0)}{c_1k}\quad(k\ge1),\qquad c_1=\frac{\varepsilon_1\varepsilon_2L}{2},$$
--   and the iterates converge to $K_*$ at a linear rate: there are $c\ge0$ and $0\le q<1$ with
--   $$\|K_j-K_*\|_F\le c\,q^j\qquad\text{for all }j. \tag{4.6}$$
--
--   This is the main convergence theorem of the paper for the discrete gradient method: although $f$ is non-convex and defined only on the stabilizing set, the method with constant-order steps converges globally and linearly to the optimal state-feedback gain.
--
--   **Formalization Note** The paper's $L$ is the constant (3.8), which is false as printed (see Theorem 3.15 in this mission). The proof (Appendix D.2) uses only that $\nabla f$ is $L$-Lipschitz on $\mathcal S_0$ (the definition of $L$-smoothness in §3.6), so $L$ is any such constant. Invariance of $\mathcal S_0$ is a conclusion, not a hypothesis. The minimum is over $j\in\{0,\dots,k\}$ and requires $k\ge1$. In (4.6) the paper uses the spectral norm; the Frobenius norm is used here, which is equivalent up to a factor absorbed in $c$. The constants $c,q$ may depend on all the data, the step sequence and $\varepsilon_1,\varepsilon_2$, as in the paper. $K_*$ is taken as a hypothesis; its existence is Corollary 3.10.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, pp. 10–11, Theorem 4.2, (4.4)–(4.6), case C = I; proof in Appendix D.2, p. 19

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

/-- Theorem 4.2 (pp. 10–11) for state feedback `C = I`, with `L` any Lipschitz constant of `∇f`
on `S₀` (the paper's `L`-smoothness, §3.6; the explicit (3.8) is false). For the gradient method
(4.4) from `K₀ ∈ S`, with `K⋆ ∈ S` a minimum point of `f` on `S`:
(i) if `0 < γⱼ ≤ 2/L` for all `j`, every iterate stays in `S₀` and (4.5) holds;
(ii) if `0 < ε₁ ≤ γⱼ ≤ 2/L − ε₂`, `ε₂ > 0`, then `∇f(Kⱼ) → 0`,
`min_{0≤j≤k} ‖∇f(Kⱼ)‖_F² ≤ f(K₀)/(c₁k)` for `k ≥ 1` with `c₁ = ε₁ε₂L/2`, and the iterates
converge linearly to `K⋆`: (4.6) `‖Kⱼ − K⋆‖_F ≤ c qʲ` for some `c ≥ 0`, `0 ≤ q < 1`. -/
theorem gradient_method_slqr_linear_rate {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hB : B ≠ 0)
    (K₀ : Matrix (Fin m) (Fin n) ℝ) (hK₀ : K₀ ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ))
    (Kstar : Matrix (Fin m) (Fin n) ℝ) (hKstar : Kstar ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ))
    (hopt : ∀ K ∈ stabSet A B (1 : Matrix (Fin n) (Fin n) ℝ), lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig Kstar ≤ lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K)
    (L : ℝ) (hLpos : 0 < L)
    (hL : ∀ K ∈ sublevel A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀, ∀ K' ∈ sublevel A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀,
      frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K - lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K') ≤ L * frobNorm (K - K'))
    (γ : ℕ → ℝ) :
    ((∀ j, 0 < γ j ∧ γ j ≤ 2 / L) →
      (∀ j, gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j ∈ sublevel A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀) ∧
      ∀ j, lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ (j + 1)) ≤
        lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j)
          - γ j * (1 - L * γ j / 2) *
            frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j)) ^ 2) ∧
    (∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → (∀ j, ε₁ ≤ γ j ∧ γ j ≤ 2 / L - ε₂) →
      Tendsto (fun j => frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j)))
        atTop (𝓝 0) ∧
      (∀ k : ℕ, 1 ≤ k →
        (Finset.range (k + 1)).inf' ⟨0, by simp⟩
            (fun j => frobNorm (lqrGrad A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j)) ^ 2)
          ≤ lqrCost A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ / (ε₁ * ε₂ * L / 2 * k)) ∧
      ∃ c q : ℝ, 0 ≤ c ∧ 0 ≤ q ∧ q < 1 ∧
        ∀ j, frobNorm (gradIter A B (1 : Matrix (Fin n) (Fin n) ℝ) Q R Sig K₀ γ j - Kstar) ≤ c * q ^ j) := by sorry

end FatkhullinPolyak.Discrete
