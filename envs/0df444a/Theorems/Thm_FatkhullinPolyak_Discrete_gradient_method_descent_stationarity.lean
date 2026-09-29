-- Prove2me | Theorems.Thm_FatkhullinPolyak_Discrete_gradient_method_descent_stationarity
-- name    : FatkhullinPolyak.Discrete.gradient_method_descent_stationarity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:42:08.408451+00:00
-- url     : https://prove2.me/theorems/bdb7a7bb-ef4a-4bd9-9eaa-81e3c0e29862
-- title:
--   Theorem 4.2 (output feedback: descent and stationarity) — the gradient method stays in $\mathcal S_0$, satisfies (4.5), and $\min_{j\le k}\|\nabla f(K_j)\|_F^2\le f(K_0)/(c_1k)$
-- statement:
--   Assume $Q,R,\Sigma\succ0$, $\operatorname{rank}C=r$, $B\ne0$ and $K_0\in\mathcal S$. Let $L>0$ be a Lipschitz constant of the gradient (3.3) on the sublevel set $\mathcal S_0$:
--   $$\|\nabla f(K)-\nabla f(K')\|_F\le L\|K-K'\|_F\qquad(K,K'\in\mathcal S_0).$$
--   Let $(\gamma_j)_{j\ge0}$ be real step sizes and $K_{j+1}=K_j-\gamma_j\nabla f(K_j)$ the gradient method (4.4) from $K_0$.
--
--   1. If $0<\gamma_j\le 2/L$ for all $j$, then every iterate $K_j$ lies in $\mathcal S_0$ and
--   $$f(K_{j+1})\le f(K_j)-\gamma_j\Big(1-\frac{L\gamma_j}{2}\Big)\|\nabla f(K_j)\|_F^2\qquad\text{for all }j. \tag{4.5}$$
--   2. If $0<\varepsilon_1\le\gamma_j\le 2/L-\varepsilon_2$ for all $j$, with $\varepsilon_2>0$, then $\nabla f(K_j)\to0$ and, with $c_1=\varepsilon_1\varepsilon_2L/2$,
--   $$\min_{0\le j\le k}\|\nabla f(K_j)\|_F^2\le\frac{f(K_0)}{c_1k}\qquad\text{for every }k\ge1 .$$
--
--   For output feedback the gradient method thus decreases the cost monotonically, never leaves the stabilizing set, and reaches stationarity at the rate $O(1/k)$.
--
--   **Formalization Note** The paper takes $L$ to be the constant (3.8) of Theorem 3.15, which is false as printed. The proof (Appendix D.2) uses only that $\nabla f$ is $L$-Lipschitz on $\mathcal S_0$, the definition of $L$-smoothness in §3.6, so $L$ is any such constant here; one exists by Theorem 3.15 (qualitative form). That the iterates stay in $\mathcal S_0$ is a conclusion (the paper calls it "the non-trivial part"), not a hypothesis. The bound is stated for $k\ge1$ ($k=0$ would divide by zero). If $\varepsilon_1>2/L-\varepsilon_2$, the step hypotheses of part 2 cannot hold, exactly as in the paper.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, pp. 10–11, Theorem 4.2, (4.4)–(4.5) and the stationarity clause (output feedback part); proof in Appendix D.2, p. 19

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

/-- Theorem 4.2, output feedback part (pp. 10–11), with `L` any Lipschitz constant of `∇f` on
`S₀` (the paper's `L`-smoothness, §3.6). For the gradient method (4.4) from `K₀ ∈ S`:
(i) if `0 < γⱼ ≤ 2/L` for all `j`, every iterate stays in `S₀` and
(4.5) `f(K_{j+1}) ≤ f(Kⱼ) − γⱼ(1 − Lγⱼ/2)‖∇f(Kⱼ)‖_F²`;
(ii) if `0 < ε₁ ≤ γⱼ ≤ 2/L − ε₂`, `ε₂ > 0`, then `∇f(Kⱼ) → 0` and
`min_{0≤j≤k} ‖∇f(Kⱼ)‖_F² ≤ f(K₀)/(c₁k)` for `k ≥ 1`, `c₁ = ε₁ε₂L/2`. -/
theorem gradient_method_descent_stationarity {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r) (hB : B ≠ 0)
    (K₀ : Matrix (Fin m) (Fin r) ℝ) (hK₀ : K₀ ∈ stabSet A B C)
    (L : ℝ) (hLpos : 0 < L)
    (hL : ∀ K ∈ sublevel A B C Q R Sig K₀, ∀ K' ∈ sublevel A B C Q R Sig K₀,
      frobNorm (lqrGrad A B C Q R Sig K - lqrGrad A B C Q R Sig K') ≤ L * frobNorm (K - K'))
    (γ : ℕ → ℝ) :
    ((∀ j, 0 < γ j ∧ γ j ≤ 2 / L) →
      (∀ j, gradIter A B C Q R Sig K₀ γ j ∈ sublevel A B C Q R Sig K₀) ∧
      ∀ j, lqrCost A B C Q R Sig (gradIter A B C Q R Sig K₀ γ (j + 1)) ≤
        lqrCost A B C Q R Sig (gradIter A B C Q R Sig K₀ γ j)
          - γ j * (1 - L * γ j / 2) *
            frobNorm (lqrGrad A B C Q R Sig (gradIter A B C Q R Sig K₀ γ j)) ^ 2) ∧
    (∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → (∀ j, ε₁ ≤ γ j ∧ γ j ≤ 2 / L - ε₂) →
      Tendsto (fun j => frobNorm (lqrGrad A B C Q R Sig (gradIter A B C Q R Sig K₀ γ j)))
        atTop (𝓝 0) ∧
      ∀ k : ℕ, 1 ≤ k →
        (Finset.range (k + 1)).inf' ⟨0, by simp⟩
            (fun j => frobNorm (lqrGrad A B C Q R Sig (gradIter A B C Q R Sig K₀ γ j)) ^ 2)
          ≤ lqrCost A B C Q R Sig K₀ / (ε₁ * ε₂ * L / 2 * k)) := by sorry

end FatkhullinPolyak.Discrete
