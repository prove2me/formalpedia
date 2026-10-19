-- Prove2me | Theorems.Thm_ApproxSparseHDSL_ExcessRisk_lemma_EC1
-- name    : ApproxSparseHDSL.ExcessRisk.lemma_EC1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:12.050494+00:00
-- url     : https://prove2.me/theorems/b1d913fd-504a-4849-9f5f-33d5ff8fb09c
-- title:
--   Lemma EC.1, p. ec41 — the empirical risk is (2σ_L + C_µ)-Lipschitz on the box with high probability
-- statement:
--   Suppose Assumption 4 holds, together with the Bernstein-like bound for $\mathcal C(Z_i)$ with constant $c > 0$ that the proof invokes, and let $\epsilon > 0$. Then there is a universal constant $\tilde c > 0$ such that
--
--   1. with probability at least $1 - 2\exp(-\tilde c\, n)$,
--   $$
--   |\mathcal L_n(\beta_1, Z_1^n) - \mathcal L_n(\beta_2, Z_1^n)| \le (2\sigma_L + \mathcal C_\mu)\,\epsilon
--   $$
--   simultaneously for all $\beta_1, \beta_2$ with $\|\beta_1\|_\infty \le R$, $\|\beta_2\|_\infty \le R$ and $\|\beta_1 - \beta_2\| \le \epsilon$;
--
--   2. $|\mathbb E[\mathcal L_n(\beta_1, Z_1^n)] - \mathbb E[\mathcal L_n(\beta_2, Z_1^n)]| \le \mathcal C_\mu\,\epsilon$ for all such $\beta_1, \beta_2$.
--
--   The lemma transfers a discretization of the box to the whole box, which is the step that turns the pointwise Bernstein bound into a uniform one in Proposition 3.
--
--   **Formalization Note** "With probability at least $1-\delta$" is the bound $\mathbb P(\text{failure}) \le \delta$ on the (outer) measure of the failure set. $\tilde c$ is quantified after $c$ and before every instance object. $\|\cdot\|$ is Euclidean.
-- source:
--   Liu, Ye & Lee, High-dimensional learning under approximate sparsity with applications to nonsmooth estimation and regularized neural networks, arXiv:1903.00616v2, p. ec41, Lemma EC.1, (EC.69)

import Mathlib
import Definitions.Def_ApproxSparseHDSL_ExcessRisk_Model

open MeasureTheory ProbabilityTheory

namespace ApproxSparseHDSL.ExcessRisk

/-- Lemma EC.1, p. ec41. Under Assumption 4 (and the Bernstein-like bound for `𝒞(Zᵢ)` with
constant `c` that its proof invokes), for every `ϵ > 0`:
(a) with probability at least `1 − 2 exp(−c̃ n)`,
`|ℒₙ(β₁) − ℒₙ(β₂)| ≤ (2σ_L + C_µ)ϵ` for all `β₁, β₂` in the box with `‖β₁ − β₂‖ ≤ ϵ`;
(b) `|E ℒₙ(β₁) − E ℒₙ(β₂)| ≤ C_µ ϵ` for all such `β₁, β₂`. -/
theorem lemma_EC1 (c : ℝ) (hc : 0 < c) :
    ∃ ct : ℝ, 0 < ct ∧
    ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
      (P : Measure Ω) (μ : Measure E) (p n : ℕ) (Z : Fin n → Ω → E)
      (L : (Fin p → ℝ) → E → ℝ) (R : ℝ) (Cfn : E → ℝ) (sigL Cmu ε : ℝ),
      IIDSample P μ Z L → Assumption4 P μ Z L R Cfn sigL Cmu →
      BernsteinC P μ Z Cfn sigL c → 0 < ε →
      P {ω | ¬ ∀ β₁ β₂ : Fin p → ℝ, InBox R β₁ → InBox R β₂ → eucl (β₁ - β₂) ≤ ε →
          |empRisk L (sample Z ω) β₁ - empRisk L (sample Z ω) β₂| ≤ (2 * sigL + Cmu) * ε}
        ≤ ENNReal.ofReal (2 * Real.exp (-(ct * n))) ∧
      ∀ β₁ β₂ : Fin p → ℝ, InBox R β₁ → InBox R β₂ → eucl (β₁ - β₂) ≤ ε →
        |∫ ω, empRisk L (sample Z ω) β₁ ∂P - ∫ ω, empRisk L (sample Z ω) β₂ ∂P| ≤ Cmu * ε := by sorry

end ApproxSparseHDSL.ExcessRisk
