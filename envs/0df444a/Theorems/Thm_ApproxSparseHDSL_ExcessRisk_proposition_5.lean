-- Prove2me | Theorems.Thm_ApproxSparseHDSL_ExcessRisk_proposition_5
-- name    : ApproxSparseHDSL.ExcessRisk.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:03.111376+00:00
-- url     : https://prove2.me/theorems/101a3388-6c51-416a-9016-83949228af96
-- title:
--   Proposition 5, p. ec24 — sparsity and excess-risk events for general ϱ
-- statement:
--   Let $a < 1$, suppose Assumptions 2, 3 and 4 hold with (12) and the $\mathcal C$-Bernstein bound for the same $c \in (0, 1/2]$, let $0 < \varrho < 1/2$, $\tilde\zeta := \ln(3eR(\sigma_L + \mathcal C_\mu))$ and
--
--   $$
--   \lambda := \sqrt{\frac{8\sigma}{c\,a\,n^{2\varrho}}\big[\ln(n^\varrho p) + \tilde\zeta\big]}.
--   $$
--
--   Let $\hat\beta$ be a random vector with $\|\hat\beta\|_\infty \le R$ and $|\hat\beta_j| \notin (0, a\lambda)$ for all $j$, almost surely. Write $s = \|\beta^*_{\varepsilon_A}\|_0$ and $\ell := \ln(n^\varrho p) + \tilde\zeta$.
--
--   1. For every $\Gamma \ge 0$ and some universal constants $\tilde c, C_1 > 0$: if $n > C_1[((\Gamma + \varepsilon_A)/\sigma)^{1/(1-2\varrho)} + s\ell]$ (EC.32) and $\mathcal L_{n,\lambda}(\hat\beta) \le \mathcal L_{n,\lambda}(\beta^*_{\varepsilon_A}) + \Gamma$ a.s., then $\mathbb P[\mathcal E_a \cap \mathcal E_b] \ge 1 - 2(p+1)e^{-\tilde c n} - 6e^{-2cn^{4\varrho - 1}}$, where
--   $$
--   \mathcal E_a = \Big\{\|\hat\beta\|_0 \le \Big\lceil \frac{2cn^{4\varrho-1}}{\ell} + \frac{2cn^{2\varrho}}{\sigma\ell}\Big(\Gamma + \varepsilon_A + \frac{2}{n^\varrho}\Big) + 8s\Big\rceil\Big\},
--   $$
--   $$
--   \mathcal E_b = \Big\{\mathbb L(\hat\beta) - L^*_g \le C_1\Big(\frac{s\ell}{n^{2\varrho}} + \sqrt{\frac{s\ell}{n}} + \frac1{n^\varrho} + \frac1{n^{1-2\varrho}} + \frac1{n^{(1-\varrho)/2}}\Big)\sigma + C_1\sqrt{\frac{\sigma(\Gamma + \varepsilon_A)}{n^{1-2\varrho}}} + \Gamma + \varepsilon_A\Big\}.
--   $$
--
--   2. For some universal constants $\tilde c, C_2 > 0$: if $n > C_2(\varepsilon_A/\sigma)^{1/(1-2\varrho)} + C_2 a^{-1}\ell\, s^{\max\{1, \frac1{2-4\varrho}, \frac1{2\varrho}\}}(\max\{1, \|\beta^*_{\varepsilon_A}\|_\infty\})^{\max\{\frac1{2-4\varrho}, \frac1{2\varrho}\}}$ (EC.35) and $\mathcal L_{n,\lambda}(\hat\beta) \le \mathcal L_{n,\lambda}(\hat\beta^{\ell_1})$ a.s., then with probability at least $1 - 2(p+1)e^{-\tilde c n} - 6e^{-2cn^{4\varrho-1}}$,
--   $$
--   \mathbb L(\hat\beta) - L^*_g \le C_2\Big[\frac{s\ell}{n^{2\varrho}} + \frac1{n^\varrho} + \frac1{n^{1-2\varrho}}\Big]\sigma + C_2\frac{s\max\{1, \|\beta^*_{\varepsilon_A}\|_\infty\}\sigma^{3/4}}{\min\{a^{1/2}n^\varrho, a^{1/4}n^{(1-\varrho)/2}\}}\ell^{1/2} + C_2\sqrt{\frac{\sigma\varepsilon_A}{n^{1-2\varrho}}} + \varepsilon_A.
--   $$
--
--   This is the probabilistic core of the paper: the second-order structure $|\hat\beta_j| \notin (0, a\lambda)$ alone yields sparsity and an excess-risk bound.
--
--   **Formalization Note** In part 2, $\hat\beta^{\ell_1}$ is a random vector that minimizes the Lasso objective (5) almost surely, as introduced in Proposition 1 (ii). The constants $\tilde c, C_1, C_2$ are quantified after $c$ and $\varrho$ ("for any $\varrho$ … some universal constants") and before every instance object and $\Gamma$. $s > 1$ is the standing convention. Probabilities are upper bounds on failure sets.
-- source:
--   Liu, Ye & Lee, High-dimensional learning under approximate sparsity with applications to nonsmooth estimation and regularized neural networks, arXiv:1903.00616v2, p. ec24, Proposition 5, (EC.32)–(EC.36)

import Mathlib
import Definitions.Def_ApproxSparseHDSL_ExcessRisk_Model

open MeasureTheory ProbabilityTheory

namespace ApproxSparseHDSL.ExcessRisk

/-- Proposition 5, pp. ec24: for `a < 1`, `ϱ ∈ (0, 1/2)` and
`λ = √(8σ/(c a n^{2ϱ}) [ln(n^ϱ p) + ζ̃])`, for every random vector `β̂` in the box with no
coordinate in `(0, aλ)` almost surely:
(i) under (EC.32) and `ℒₙ,λ(β̂) ≤ ℒₙ,λ(β*_εA) + Γ` a.s., the events `ℰ_a` (EC.33) and `ℰ_b`
(EC.34) hold jointly with probability at least `1 − 2(p+1)exp(−c̃n) − 6exp(−2cn^{4ϱ−1})`;
(ii) for an a.s. Lasso minimizer `β̂^{ℓ₁}` (as in Proposition 1 (ii)), under (EC.35) and
`ℒₙ,λ(β̂) ≤ ℒₙ,λ(β̂^{ℓ₁})` a.s., the bound (EC.36) holds with the same probability. -/
theorem proposition_5 (c : ℝ) (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (rho : ℝ) (hrho : 0 < rho) (hrho2 : rho < 1 / 2) :
    (∃ ct C1 : ℝ, 0 < ct ∧ 0 < C1 ∧
      ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
        (P : Measure Ω) (μ : Measure E) (p n : ℕ) (Z : Fin n → Ω → E)
        (L : (Fin p → ℝ) → E → ℝ) (R σ : ℝ) (Cfn : E → ℝ) (sigL Cmu epsA Lg : ℝ)
        (betaStar : Fin p → ℝ) (a lam : ℝ) (betaHat : Ω → Fin p → ℝ) (Γ : ℝ),
        IIDSample P μ Z L → Assumption2 μ L R epsA Lg betaStar → 1 < l0 betaStar →
        Assumption3 P μ Z L R σ → Assumption4 P μ Z L R Cfn sigL Cmu →
        Bernstein12 P μ Z L R σ c → BernsteinC P μ Z Cfn sigL c →
        0 < a → a < 1 → lam = lamRho σ c a n p rho (zetaT R sigL Cmu) →
        Measurable betaHat →
        (∀ᵐ ω ∂P, InBox R (betaHat ω) ∧ ∀ j, |betaHat ω j| ∉ Set.Ioo 0 (a * lam)) →
        0 ≤ Γ →
        (n : ℝ) > C1 * (((Γ + epsA) / σ) ^ (1 / (1 - 2 * rho))
          + l0 betaStar * (Real.log ((n : ℝ) ^ rho * p) + zetaT R sigL Cmu)) →
        (∀ᵐ ω ∂P, regRisk a lam L (sample Z ω) (betaHat ω)
            ≤ regRisk a lam L (sample Z ω) betaStar + Γ) →
        P {ω | ¬ (l0 (betaHat ω) ≤
              ⌈2 * c * (n : ℝ) ^ (4 * rho - 1)
                  / (Real.log ((n : ℝ) ^ rho * p) + zetaT R sigL Cmu)
                + 2 * c * (n : ℝ) ^ (2 * rho)
                  / (σ * (Real.log ((n : ℝ) ^ rho * p) + zetaT R sigL Cmu))
                  * (Γ + epsA + 2 / (n : ℝ) ^ rho)
                + 8 * l0 betaStar⌉₊ ∧
            popRisk μ L (betaHat ω) - Lg ≤
              C1 * (l0 betaStar * (Real.log ((n : ℝ) ^ rho * p) + zetaT R sigL Cmu)
                      / (n : ℝ) ^ (2 * rho)
                    + Real.sqrt (l0 betaStar
                        * (Real.log ((n : ℝ) ^ rho * p) + zetaT R sigL Cmu) / n)
                    + 1 / (n : ℝ) ^ rho + 1 / (n : ℝ) ^ (1 - 2 * rho)
                    + 1 / (n : ℝ) ^ ((1 - rho) / 2)) * σ
                + C1 * Real.sqrt (σ * (Γ + epsA) / (n : ℝ) ^ (1 - 2 * rho)) + Γ + epsA)}
          ≤ ENNReal.ofReal (2 * (p + 1) * Real.exp (-(ct * n))
              + 6 * Real.exp (-(2 * c * (n : ℝ) ^ (4 * rho - 1))))) ∧
    (∃ ct C2 : ℝ, 0 < ct ∧ 0 < C2 ∧
      ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
        (P : Measure Ω) (μ : Measure E) (p n : ℕ) (Z : Fin n → Ω → E)
        (L : (Fin p → ℝ) → E → ℝ) (R σ : ℝ) (Cfn : E → ℝ) (sigL Cmu epsA Lg : ℝ)
        (betaStar : Fin p → ℝ) (a lam : ℝ) (betaHat betaL1 : Ω → Fin p → ℝ),
        IIDSample P μ Z L → Assumption2 μ L R epsA Lg betaStar → 1 < l0 betaStar →
        Assumption3 P μ Z L R σ → Assumption4 P μ Z L R Cfn sigL Cmu →
        Bernstein12 P μ Z L R σ c → BernsteinC P μ Z Cfn sigL c →
        0 < a → a < 1 → lam = lamRho σ c a n p rho (zetaT R sigL Cmu) →
        Measurable betaHat →
        (∀ᵐ ω ∂P, InBox R (betaHat ω) ∧ ∀ j, |betaHat ω j| ∉ Set.Ioo 0 (a * lam)) →
        (∀ᵐ ω ∂P, ∀ β : Fin p → ℝ,
            lassoObj lam L (sample Z ω) (betaL1 ω) ≤ lassoObj lam L (sample Z ω) β) →
        (n : ℝ) > C2 * (epsA / σ) ^ (1 / (1 - 2 * rho))
          + C2 * a⁻¹ * (Real.log ((n : ℝ) ^ rho * p) + zetaT R sigL Cmu)
            * (l0 betaStar : ℝ) ^ (max 1 (max (1 / (2 - 4 * rho)) (1 / (2 * rho))))
            * (max 1 (supNorm betaStar)) ^ (max (1 / (2 - 4 * rho)) (1 / (2 * rho))) →
        (∀ᵐ ω ∂P, regRisk a lam L (sample Z ω) (betaHat ω)
            ≤ regRisk a lam L (sample Z ω) (betaL1 ω)) →
        P {ω | ¬ (popRisk μ L (betaHat ω) - Lg ≤
            C2 * (l0 betaStar * (Real.log ((n : ℝ) ^ rho * p) + zetaT R sigL Cmu)
                    / (n : ℝ) ^ (2 * rho)
                  + 1 / (n : ℝ) ^ rho + 1 / (n : ℝ) ^ (1 - 2 * rho)) * σ
              + C2 * (l0 betaStar * max 1 (supNorm betaStar) * σ ^ (3 / 4 : ℝ))
                  / min (a ^ (1 / 2 : ℝ) * (n : ℝ) ^ rho)
                        (a ^ (1 / 4 : ℝ) * (n : ℝ) ^ ((1 - rho) / 2))
                  * (Real.log ((n : ℝ) ^ rho * p) + zetaT R sigL Cmu) ^ (1 / 2 : ℝ)
              + C2 * Real.sqrt (σ * epsA / (n : ℝ) ^ (1 - 2 * rho)) + epsA)}
          ≤ ENNReal.ofReal (2 * (p + 1) * Real.exp (-(ct * n))
              + 6 * Real.exp (-(2 * c * (n : ℝ) ^ (4 * rho - 1))))) := by sorry

end ApproxSparseHDSL.ExcessRisk
