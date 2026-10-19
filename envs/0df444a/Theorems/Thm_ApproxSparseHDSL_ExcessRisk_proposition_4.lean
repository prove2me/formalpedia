-- Prove2me | Theorems.Thm_ApproxSparseHDSL_ExcessRisk_proposition_4
-- name    : ApproxSparseHDSL.ExcessRisk.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:10.585429+00:00
-- url     : https://prove2.me/theorems/c535a0a0-8495-4625-9734-fa2421d0b509
-- title:
--   Proposition 4, p. ec22, with the printed σ_C read as σ_L — sparsity of β̂ with high probability
-- statement:
--   Suppose Assumptions 2, 3 and 4 hold, with (12) and the Bernstein bound for $\mathcal C(Z_i)$ for the same $c \in (0, 1/2]$. Let $a, \lambda > 0$, $\Gamma \ge 0$, $\epsilon \in (0, 1]$ and $\zeta_1(\epsilon) := \ln(3(\sigma_L + \mathcal C_\mu)peR/\epsilon)$. Let $\hat\beta$ be a random vector with $\|\hat\beta\|_\infty \le R$ and $|\hat\beta_j| \notin (0, a\lambda)$ for all $j$, almost surely, and
--
--   $$
--   \mathcal L_{n,\lambda}(\hat\beta, Z_1^n) \le \mathcal L_{n,\lambda}(\beta^*_{\varepsilon_A}, Z_1^n) + \Gamma \quad \text{w.p. } 1. \tag{EC.26}
--   $$
--
--   For a positive integer $p'_u > s$, if
--
--   $$
--   (p' - s)\,P_\lambda(a\lambda) > \frac{4\sigma}{cn}\zeta_1(\epsilon)\,p' + \frac{2\sigma}{\sqrt n}\sqrt{\frac{2p'}{c}\zeta_1(\epsilon)} + \Gamma + 2\epsilon + \varepsilon_A \tag{EC.27}
--   $$
--
--   for all $p'$ with $p'_u \le p' \le p$, then for some $\tilde c > 0$
--
--   $$
--   \mathbb P\big[\|\hat\beta\|_0 \le p'_u - 1\big] \ge 1 - 2p\exp(-\tilde c n) - 4\exp(-p'_u\zeta_1(\epsilon)).
--   $$
--
--   Near-optimality of $\hat\beta$ in the regularized objective thus forces it to be sparse, without any restricted strong convexity.
--
--   **Correction.** The paper prints $\sigma_C$ in $\zeta_1(\epsilon)$; $\sigma_L$ is meant (it is Proposition 3's $\zeta_1$, which the proof uses on p. ec22). The statement uses $\sigma_L$.
--
--   **Formalization Note** $s = \|\beta^*_{\varepsilon_A}\|_0 > 1$ (the paper's standing convention). The probability is an upper bound on the failure set; $p'_u - 1$ is natural-number subtraction, harmless since $p'_u > s > 1$.
-- source:
--   Liu, Ye & Lee, High-dimensional learning under approximate sparsity with applications to nonsmooth estimation and regularized neural networks, arXiv:1903.00616v2, p. ec22, Proposition 4, (EC.26), (EC.27)

import Mathlib
import Definitions.Def_ApproxSparseHDSL_ExcessRisk_Model

open MeasureTheory ProbabilityTheory

namespace ApproxSparseHDSL.ExcessRisk

/-- Proposition 4, p. ec22, with the printed `σ_C` in `ζ₁(ϵ)` read as `σ_L`: if `β̂` lies in the
box and has no coordinate with `|β̂ⱼ| ∈ (0, aλ)` almost surely, satisfies (EC.26) almost surely,
and (EC.27) holds for every `p′` with `p′_u ≤ p′ ≤ p`, then `‖β̂‖₀ ≤ p′_u − 1` with probability
at least `1 − 2p exp(−c̃ n) − 4 exp(−p′_u ζ₁(ϵ))`. -/
theorem proposition_4 (c : ℝ) (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    ∃ ct : ℝ, 0 < ct ∧
    ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
      (P : Measure Ω) (μ : Measure E) (p n : ℕ) (Z : Fin n → Ω → E)
      (L : (Fin p → ℝ) → E → ℝ) (R σ : ℝ) (Cfn : E → ℝ) (sigL Cmu epsA Lg : ℝ)
      (betaStar : Fin p → ℝ) (a lam Γ ε : ℝ) (betaHat : Ω → Fin p → ℝ) (p'u : ℕ),
      IIDSample P μ Z L → Assumption2 μ L R epsA Lg betaStar → 1 < l0 betaStar →
      Assumption3 P μ Z L R σ → Assumption4 P μ Z L R Cfn sigL Cmu →
      Bernstein12 P μ Z L R σ c → BernsteinC P μ Z Cfn sigL c →
      0 < a → 0 < lam → 0 ≤ Γ → 0 < ε → ε ≤ 1 →
      Measurable betaHat →
      (∀ᵐ ω ∂P, InBox R (betaHat ω) ∧ ∀ j, |betaHat ω j| ∉ Set.Ioo 0 (a * lam)) →
      (∀ᵐ ω ∂P, regRisk a lam L (sample Z ω) (betaHat ω)
          ≤ regRisk a lam L (sample Z ω) betaStar + Γ) →
      l0 betaStar < p'u →
      (∀ p' : ℕ, p'u ≤ p' → p' ≤ p →
        ((p' : ℝ) - l0 betaStar) * mcp a lam (a * lam) >
          4 * σ / (c * n) * zeta1 p R sigL Cmu ε * p'
            + 2 * σ / Real.sqrt n * Real.sqrt (2 * p' / c * zeta1 p R sigL Cmu ε)
            + Γ + 2 * ε + epsA) →
      P {ω | ¬ l0 (betaHat ω) ≤ p'u - 1}
        ≤ ENNReal.ofReal (2 * p * Real.exp (-(ct * n))
            + 4 * Real.exp (-(p'u * zeta1 p R sigL Cmu ε))) := by sorry

end ApproxSparseHDSL.ExcessRisk
