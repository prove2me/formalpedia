-- Prove2me | Theorems.Thm_ApproxSparseHDSL_ExcessRisk_proposition_1
-- name    : ApproxSparseHDSL.ExcessRisk.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:11.800984+00:00
-- url     : https://prove2.me/theorems/a396c4ff-3445-4e69-8e92-68c436ec93ab
-- title:
--   Proposition 1, pp. 15–16, with a < 1 added (Proposition 5's hypothesis) — excess risk of S³ONC solutions for general ϱ
-- statement:
--   Suppose Assumptions 2, 3 and 4 hold, with (12) and the $\mathcal C$-Bernstein bound for the same constant $c \in (0, 1/2]$. Let $0 < \varrho < 1/2$, $0 < a < 1/U_L$, $a < 1$, $\tilde\zeta := \ln(3eR(\sigma_L + \mathcal C_\mu))$ and
--
--   $$
--   \lambda := \sqrt{\frac{8\sigma}{c\,a\,n^{2\varrho}}\big[\ln(n^\varrho p) + \tilde\zeta\big]}.
--   $$
--
--   Let $\hat\beta$ be a random vector with $\|\hat\beta\|_\infty \le R$ that satisfies the S³ONC$(Z_1^n)$ of (3) almost surely. Write $s = \|\beta^*_{\varepsilon_A}\|_0$ and $\ell = \ln(n^\varrho p) + \tilde\zeta$.
--
--   1. For every $\Gamma \ge 0$ and some universal constant $C_1 > 0$: if $n > C_1[((\Gamma + \varepsilon_A)/\sigma)^{1/(1-2\varrho)} + s\ell]$ (15) and $\mathcal L_{n,\lambda}(\hat\beta, Z_1^n) \le \mathcal L_{n,\lambda}(\beta^*_{\varepsilon_A}, Z_1^n) + \Gamma$ almost surely, then
--   $$
--   \mathbb L(\hat\beta) - L^*_g \le C_1\Big(\frac{s\ell}{n^{2\varrho}} + \sqrt{\frac{s\ell}{n}} + \frac1{n^\varrho} + \frac1{n^{1-2\varrho}} + \frac1{n^{(1-\varrho)/2}}\Big)\sigma + C_1\sqrt{\frac{\sigma(\Gamma + \varepsilon_A)}{n^{1-2\varrho}}} + \Gamma + \varepsilon_A \tag{16}
--   $$
--   with probability at least $1 - 2(p+1)\exp(-n/C_1) - 6\exp(-2cn^{4\varrho-1})$.
--
--   2. If almost surely the Lasso (5) has a finite optimal solution $\hat\beta^{\ell_1}$, then for some universal constant $C_2 > 0$: if $n > C_2(\varepsilon_A/\sigma)^{1/(1-2\varrho)} + C_2 a^{-1}\ell\, s^{\max\{1, \frac1{2-4\varrho}, \frac1{2\varrho}\}}(\max\{1, \|\beta^*_{\varepsilon_A}\|_\infty\})^{\max\{\frac1{2-4\varrho}, \frac1{2\varrho}\}}$ (17) and $\mathcal L_{n,\lambda}(\hat\beta, Z_1^n) \le \mathcal L_{n,\lambda}(\hat\beta^{\ell_1}, Z_1^n)$ almost surely, then
--   $$
--   \mathbb L(\hat\beta) - L^*_g \le C_2\Big[\frac{s\ell}{n^{2\varrho}} + \frac1{n^\varrho} + \frac1{n^{1-2\varrho}}\Big]\sigma + C_2\frac{s\max\{1, \|\beta^*_{\varepsilon_A}\|_\infty\}\sigma^{3/4}}{\min\{a^{1/2}n^\varrho, a^{1/4}n^{(1-\varrho)/2}\}}\ell^{1/2} + C_2\sqrt{\frac{\sigma\varepsilon_A}{n^{1-2\varrho}}} + \varepsilon_A \tag{18}
--   $$
--   with probability at least $1 - 2(p+1)\exp(-n/C_2) - 6\exp(-2cn^{4\varrho-1})$.
--
--   The paper calls this its most general result: it needs neither convexity nor restricted strong convexity, and the free parameter $\varrho$ trades the polynomial rate against the sample size.
--
--   **Correction.** The hypothesis $a < 1$ is added. The printed proof (p. ec20) derives Proposition 1 from Proposition 2 and Proposition 5, and Proposition 5 assumes $a < 1$; Proposition 1 itself only assumes $a < 1/U_L$, and (11) only gives $U_L > 0$.
--
--   **Formalization Note** $C_1, C_2$ are quantified after $c$ and $\varrho$ and before every instance object and $\Gamma$. $\hat\beta^{\ell_1}$ is a random vector minimizing (5) almost surely. $s > 1$ is the standing convention. Probabilities are upper bounds on failure sets.
-- source:
--   Liu, Ye & Lee, High-dimensional learning under approximate sparsity with applications to nonsmooth estimation and regularized neural networks, arXiv:1903.00616v2, pp. 15–16, Proposition 1, (15)–(18); p. ec24, Proposition 5 (hypothesis a < 1)

import Mathlib
import Definitions.Def_ApproxSparseHDSL_ExcessRisk_Model

open MeasureTheory ProbabilityTheory

namespace ApproxSparseHDSL.ExcessRisk

/-- Proposition 1, pp. 15–16, with `a < 1` added (Proposition 5's hypothesis, which the printed
proof of Proposition 1 invokes, p. ec20). For `ϱ ∈ (0, 1/2)`, `a < 1/U_L` and
`λ = √(8σ/(c a n^{2ϱ}) [ln(n^ϱ p) + ζ̃])`, every random vector `β̂` with `‖β̂‖∞ ≤ R` satisfying
the S³ONC almost surely obeys:
(i) under (15) and `ℒₙ,λ(β̂) ≤ ℒₙ,λ(β*_εA) + Γ` a.s., the excess-risk bound (16);
(ii) for an a.s. Lasso minimizer `β̂^{ℓ₁}`, under (17) and `ℒₙ,λ(β̂) ≤ ℒₙ,λ(β̂^{ℓ₁})` a.s., the
bound (18); each with probability at least `1 − 2(p+1)exp(−n/C) − 6exp(−2cn^{4ϱ−1})`. -/
theorem proposition_1 (c : ℝ) (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (rho : ℝ) (hrho : 0 < rho) (hrho2 : rho < 1 / 2) :
    (∃ C1 : ℝ, 0 < C1 ∧
      ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
        (P : Measure Ω) (μ : Measure E) (p n : ℕ) (Z : Fin n → Ω → E)
        (L : (Fin p → ℝ) → E → ℝ) (UL R σ : ℝ) (Cfn : E → ℝ) (sigL Cmu epsA Lg : ℝ)
        (betaStar : Fin p → ℝ) (a lam : ℝ) (betaHat : Ω → Fin p → ℝ) (Γ : ℝ),
        IIDSample P μ Z L → Smooth11 μ L UL →
        Assumption2 μ L R epsA Lg betaStar → 1 < l0 betaStar →
        Assumption3 P μ Z L R σ → Assumption4 P μ Z L R Cfn sigL Cmu →
        Bernstein12 P μ Z L R σ c → BernsteinC P μ Z Cfn sigL c →
        0 < a → a < 1 / UL → a < 1 → lam = lamRho σ c a n p rho (zetaT R sigL Cmu) →
        Measurable betaHat → (∀ᵐ ω ∂P, InBox R (betaHat ω)) →
        (∀ᵐ ω ∂P, S3ONC UL a lam L (sample Z ω) (betaHat ω)) →
        0 ≤ Γ →
        (n : ℝ) > C1 * (((Γ + epsA) / σ) ^ (1 / (1 - 2 * rho))
          + l0 betaStar * (Real.log ((n : ℝ) ^ rho * p) + zetaT R sigL Cmu)) →
        (∀ᵐ ω ∂P, regRisk a lam L (sample Z ω) (betaHat ω)
            ≤ regRisk a lam L (sample Z ω) betaStar + Γ) →
        P {ω | ¬ (popRisk μ L (betaHat ω) - Lg ≤
            C1 * (l0 betaStar * (Real.log ((n : ℝ) ^ rho * p) + zetaT R sigL Cmu)
                    / (n : ℝ) ^ (2 * rho)
                  + Real.sqrt (l0 betaStar
                      * (Real.log ((n : ℝ) ^ rho * p) + zetaT R sigL Cmu) / n)
                  + 1 / (n : ℝ) ^ rho + 1 / (n : ℝ) ^ (1 - 2 * rho)
                  + 1 / (n : ℝ) ^ ((1 - rho) / 2)) * σ
              + C1 * Real.sqrt (σ * (Γ + epsA) / (n : ℝ) ^ (1 - 2 * rho)) + Γ + epsA)}
          ≤ ENNReal.ofReal (2 * (p + 1) * Real.exp (-(n / C1))
              + 6 * Real.exp (-(2 * c * (n : ℝ) ^ (4 * rho - 1))))) ∧
    (∃ C2 : ℝ, 0 < C2 ∧
      ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
        (P : Measure Ω) (μ : Measure E) (p n : ℕ) (Z : Fin n → Ω → E)
        (L : (Fin p → ℝ) → E → ℝ) (UL R σ : ℝ) (Cfn : E → ℝ) (sigL Cmu epsA Lg : ℝ)
        (betaStar : Fin p → ℝ) (a lam : ℝ) (betaHat betaL1 : Ω → Fin p → ℝ),
        IIDSample P μ Z L → Smooth11 μ L UL →
        Assumption2 μ L R epsA Lg betaStar → 1 < l0 betaStar →
        Assumption3 P μ Z L R σ → Assumption4 P μ Z L R Cfn sigL Cmu →
        Bernstein12 P μ Z L R σ c → BernsteinC P μ Z Cfn sigL c →
        0 < a → a < 1 / UL → a < 1 → lam = lamRho σ c a n p rho (zetaT R sigL Cmu) →
        Measurable betaHat → (∀ᵐ ω ∂P, InBox R (betaHat ω)) →
        (∀ᵐ ω ∂P, S3ONC UL a lam L (sample Z ω) (betaHat ω)) →
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
          ≤ ENNReal.ofReal (2 * (p + 1) * Real.exp (-(n / C2))
              + 6 * Real.exp (-(2 * c * (n : ℝ) ^ (4 * rho - 1))))) := by sorry

end ApproxSparseHDSL.ExcessRisk
