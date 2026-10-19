-- Prove2me | Theorems.Thm_ApproxSparseHDSL_ExcessRisk_theorem_1
-- name    : ApproxSparseHDSL.ExcessRisk.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:21.157009+00:00
-- url     : https://prove2.me/theorems/4fe5f8f6-984d-466b-89bb-98992d4a7fa7
-- title:
--   Theorem 1, p. 18, with a < 1 added (Proposition 5's hypothesis) — excess risk of S³ONC solutions under approximate sparsity
-- statement:
--   Let $Z_1, \dots, Z_n$ be i.i.d. observations and $L(\beta, z)$ a loss on $\beta \in \mathbb R^p$ whose coordinate partial derivatives are $U_L$-Lipschitz (11). Suppose Assumptions 1, 3 and 4 hold, and (12) and the $\mathcal C$-Bernstein bound hold with constant $c \in (0, 1/2]$. Let $0 < a < 1/U_L$, $a < 1$, $\tilde\zeta := \ln(3eR(\sigma_L + \mathcal C_\mu))$ and
--
--   $$
--   \lambda := \sqrt{\frac{8\sigma}{c\,a\,n^{2/3}}\big[\ln(n^{2/3}p) + \tilde\zeta\big]}.
--   $$
--
--   Let $\hat\beta$ be any random vector with $\|\hat\beta\|_\infty \le R$ that satisfies the S³ONC$(Z_1^n)$ of (3) almost surely, and write $s = \|\beta^*_{\varepsilon_A}\|_0$.
--
--   1. For every $\Gamma \ge 0$ there is a universal constant $C_3 > 0$ (independent of $\Gamma$ and of the problem) such that, if
--   $$
--   n > C_3\Big[\Big(\frac{\Gamma + \varepsilon_A}{\sigma}\Big)^3 + s(\ln(np) + \tilde\zeta)\Big] \tag{19}
--   $$
--   and $\mathcal L_{n,\lambda}(\hat\beta, Z_1^n) \le \mathcal L_{n,\lambda}(\beta^*_{\varepsilon_A}, Z_1^n) + \Gamma$ almost surely, then
--   $$
--   \mathbb L(\hat\beta) - \inf_\beta \mathbb L(\beta) \le C_3\sigma\Big[\frac{s(\ln(np) + \tilde\zeta)}{n^{2/3}} + \sqrt{\frac{s(\ln(np) + \tilde\zeta)}{n}} + \frac1{n^{1/3}}\Big] + C_3\sqrt{\frac{\sigma(\Gamma + \varepsilon_A)}{n^{1/3}}} + \Gamma + \varepsilon_A \tag{20}
--   $$
--   with probability at least $1 - 2(p+1)\exp(-n/C_3) - 6\exp(-n^{1/3}/C_3)$.
--
--   2. If almost surely the Lasso (5) has a finite optimal solution $\hat\beta^{\ell_1}$, there is a universal constant $C_4 > 0$ such that, if
--   $$
--   n > C_4\Big(\frac{\varepsilon_A}{\sigma}\Big)^3 + C_4 a^{-1}[\ln(np) + \tilde\zeta]\, s^{3/2}\max\{1, \|\beta^*_{\varepsilon_A}\|_\infty^{3/2}\} \tag{21}
--   $$
--   and $\mathcal L_{n,\lambda}(\hat\beta, Z_1^n) \le \mathcal L_{n,\lambda}(\hat\beta^{\ell_1}, Z_1^n)$ almost surely, then
--   $$
--   \mathbb L(\hat\beta) - \inf_\beta \mathbb L(\beta) \le C_4 a^{-1/2} s\sigma\Big[\frac{\ln(np) + \tilde\zeta}{n^{2/3}} + \frac{\max\{1, \|\beta^*_{\varepsilon_A}\|_\infty\}\sqrt{\ln(np) + \tilde\zeta}}{n^{1/3}}\Big] + C_4\sqrt{\frac{\sigma\varepsilon_A}{n^{1/3}}} + \varepsilon_A \tag{22}
--   $$
--   with probability at least $1 - 2(p+1)\exp(-n/C_4) - 6\exp(-n^{1/3}/C_4)$.
--
--   This is the paper's headline result: any second-order stationary point of the MCP-regularized empirical risk has excess risk poly-logarithmic in the dimension $p$, under approximate sparsity and without restricted strong convexity.
--
--   **Correction.** The hypothesis $a < 1$ is added. The printed proof invokes Proposition 1 with $\varrho = 1/3$, whose proof uses Proposition 5, which assumes $a < 1$; Theorem 1 itself only assumes $a < 1/U_L$, and (11) only gives $U_L > 0$. Whether Theorem 1 fails without $a < 1$ is not known. The tuning parameter $\lambda$ is Theorem 1's as printed, with $\ln(n^{2/3}p)$; Proposition 1 at $\varrho = 1/3$ has $\ln(n^{1/3}p)$, so the printed one-line proof does not apply literally.
--
--   **Formalization Note** The Bernstein constant $c$ of (12) is quantified first; $C_3$ and $C_4$ may depend on it (it is absolute), and are quantified before every problem object ($p$, $n$, the distribution, $L$, $\hat\beta$) and before $\Gamma$. Probabilities are upper bounds on failure sets. $\inf_\beta \mathbb L(\beta)$ is a genuine infimum because $\mathbb L$ is bounded below. $\|\cdot\|$ in Assumption 4 is Euclidean. $s > 1$ is the paper's standing convention (p. 5). $\hat\beta^{\ell_1}$ is any random vector minimizing (5) almost surely.
-- source:
--   Liu, Ye & Lee, High-dimensional learning under approximate sparsity with applications to nonsmooth estimation and regularized neural networks, arXiv:1903.00616v2, p. 18, Theorem 1, (19)–(22); p. ec24, Proposition 5 (hypothesis a < 1)

import Mathlib
import Definitions.Def_ApproxSparseHDSL_ExcessRisk_Model

open MeasureTheory ProbabilityTheory

namespace ApproxSparseHDSL.ExcessRisk

/-- Theorem 1, p. 18, with `a < 1` added (Proposition 5's hypothesis, carried up through
Proposition 1). Let `a < 1/U_L` and `λ = √(8σ/(c a n^{2/3}) [ln(n^{2/3} p) + ζ̃])` for the
Bernstein constant `c` of (12). Under Assumptions 1, 3 and 4, every random vector `β̂` with
`‖β̂‖∞ ≤ R` satisfying the S³ONC almost surely obeys:
(i) for every `Γ ≥ 0`, under (19) and `ℒₙ,λ(β̂) ≤ ℒₙ,λ(β*_εA) + Γ` a.s., the excess-risk bound
(20) with probability at least `1 − 2(p+1)exp(−n/C₃) − 6exp(−n^{1/3}/C₃)`;
(ii) for an a.s. Lasso minimizer `β̂^{ℓ₁}` of (5), under (21) and `ℒₙ,λ(β̂) ≤ ℒₙ,λ(β̂^{ℓ₁})`
a.s., the bound (22) with probability at least `1 − 2(p+1)exp(−n/C₄) − 6exp(−n^{1/3}/C₄)`. -/
theorem theorem_1 (c : ℝ) (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    (∃ C3 : ℝ, 0 < C3 ∧
      ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
        (P : Measure Ω) (μ : Measure E) (p n : ℕ) (Z : Fin n → Ω → E)
        (L : (Fin p → ℝ) → E → ℝ) (UL R σ : ℝ) (Cfn : E → ℝ) (sigL Cmu epsA : ℝ)
        (betaStar : Fin p → ℝ) (a lam : ℝ) (betaHat : Ω → Fin p → ℝ) (Γ : ℝ),
        IIDSample P μ Z L → Smooth11 μ L UL →
        Assumption1 μ L R epsA betaStar → 1 < l0 betaStar →
        Assumption3 P μ Z L R σ → Assumption4 P μ Z L R Cfn sigL Cmu →
        Bernstein12 P μ Z L R σ c → BernsteinC P μ Z Cfn sigL c →
        0 < a → a < 1 / UL → a < 1 → lam = lamThm1 σ c a n p (zetaT R sigL Cmu) →
        Measurable betaHat → (∀ᵐ ω ∂P, InBox R (betaHat ω)) →
        (∀ᵐ ω ∂P, S3ONC UL a lam L (sample Z ω) (betaHat ω)) →
        0 ≤ Γ →
        (n : ℝ) > C3 * (((Γ + epsA) / σ) ^ 3
          + l0 betaStar * (Real.log ((n : ℝ) * p) + zetaT R sigL Cmu)) →
        (∀ᵐ ω ∂P, regRisk a lam L (sample Z ω) (betaHat ω)
            ≤ regRisk a lam L (sample Z ω) betaStar + Γ) →
        P {ω | ¬ (popRisk μ L (betaHat ω) - ⨅ β, popRisk μ L β ≤
            C3 * σ * (l0 betaStar * (Real.log ((n : ℝ) * p) + zetaT R sigL Cmu)
                        / (n : ℝ) ^ (2 / 3 : ℝ)
                      + Real.sqrt (l0 betaStar
                          * (Real.log ((n : ℝ) * p) + zetaT R sigL Cmu) / n)
                      + 1 / (n : ℝ) ^ (1 / 3 : ℝ))
              + C3 * Real.sqrt (σ * (Γ + epsA) / (n : ℝ) ^ (1 / 3 : ℝ)) + Γ + epsA)}
          ≤ ENNReal.ofReal (2 * (p + 1) * Real.exp (-(n / C3))
              + 6 * Real.exp (-((n : ℝ) ^ (1 / 3 : ℝ) / C3)))) ∧
    (∃ C4 : ℝ, 0 < C4 ∧
      ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
        (P : Measure Ω) (μ : Measure E) (p n : ℕ) (Z : Fin n → Ω → E)
        (L : (Fin p → ℝ) → E → ℝ) (UL R σ : ℝ) (Cfn : E → ℝ) (sigL Cmu epsA : ℝ)
        (betaStar : Fin p → ℝ) (a lam : ℝ) (betaHat betaL1 : Ω → Fin p → ℝ),
        IIDSample P μ Z L → Smooth11 μ L UL →
        Assumption1 μ L R epsA betaStar → 1 < l0 betaStar →
        Assumption3 P μ Z L R σ → Assumption4 P μ Z L R Cfn sigL Cmu →
        Bernstein12 P μ Z L R σ c → BernsteinC P μ Z Cfn sigL c →
        0 < a → a < 1 / UL → a < 1 → lam = lamThm1 σ c a n p (zetaT R sigL Cmu) →
        Measurable betaHat → (∀ᵐ ω ∂P, InBox R (betaHat ω)) →
        (∀ᵐ ω ∂P, S3ONC UL a lam L (sample Z ω) (betaHat ω)) →
        (∀ᵐ ω ∂P, ∀ β : Fin p → ℝ,
            lassoObj lam L (sample Z ω) (betaL1 ω) ≤ lassoObj lam L (sample Z ω) β) →
        (n : ℝ) > C4 * (epsA / σ) ^ 3
          + C4 * a⁻¹ * (Real.log ((n : ℝ) * p) + zetaT R sigL Cmu)
            * (l0 betaStar : ℝ) ^ (3 / 2 : ℝ)
            * max 1 (supNorm betaStar ^ (3 / 2 : ℝ)) →
        (∀ᵐ ω ∂P, regRisk a lam L (sample Z ω) (betaHat ω)
            ≤ regRisk a lam L (sample Z ω) (betaL1 ω)) →
        P {ω | ¬ (popRisk μ L (betaHat ω) - ⨅ β, popRisk μ L β ≤
            C4 * a ^ (-(1 / 2) : ℝ) * l0 betaStar * σ
                * ((Real.log ((n : ℝ) * p) + zetaT R sigL Cmu) / (n : ℝ) ^ (2 / 3 : ℝ)
                  + max 1 (supNorm betaStar)
                      * Real.sqrt (Real.log ((n : ℝ) * p) + zetaT R sigL Cmu)
                      / (n : ℝ) ^ (1 / 3 : ℝ))
              + C4 * Real.sqrt (σ * epsA / (n : ℝ) ^ (1 / 3 : ℝ)) + epsA)}
          ≤ ENNReal.ofReal (2 * (p + 1) * Real.exp (-(n / C4))
              + 6 * Real.exp (-((n : ℝ) ^ (1 / 3 : ℝ) / C4)))) := by sorry

end ApproxSparseHDSL.ExcessRisk
