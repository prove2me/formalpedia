-- Prove2me | Theorems.Thm_ApproxSparseHDSL_ExcessRisk_proposition_3
-- name    : ApproxSparseHDSL.ExcessRisk.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:10.885773+00:00
-- url     : https://prove2.me/theorems/8573402e-5786-49c8-9505-a5975e09a97b
-- title:
--   Proposition 3, p. ec20 — uniform deviation of the empirical risk over sparse vectors in the box
-- statement:
--   Suppose Assumptions 3 and 4 hold, with (12) and the Bernstein bound for $\mathcal C(Z_i)$ for the same constant $c \in (0, 1/2]$. Let $\epsilon \in (0, 1]$, let $p' > s$, and set
--
--   $$
--   \zeta_1(\epsilon) := \ln\Big(\frac{3(\sigma_L + \mathcal C_\mu)\,p\,eR}{\epsilon}\Big), \qquad \mathcal B_{p', R} := \{\beta \in \mathbb R^p : \|\beta\|_\infty \le R,\ \|\beta\|_0 \le p'\}.
--   $$
--
--   Then for some universal constant $\tilde c > 0$,
--
--   $$
--   \sup_{\beta \in \mathcal B_{p',R}} \Big|\frac1n\sum_{i=1}^n L(\beta, Z_i) - \mathbb L(\beta)\Big| \le \frac{\sigma}{\sqrt n}\sqrt{\frac{2p'}{c}\zeta_1(\epsilon)} + \frac{\sigma}{n}\cdot\frac{2p'}{c}\zeta_1(\epsilon) + \epsilon
--   $$
--
--   with probability at least $1 - 2\exp(-p'\zeta_1(\epsilon)) - 2\exp(-\tilde c n)$.
--
--   This is the uniform law of large numbers over sparse parameter vectors; its deviation grows only logarithmically in the dimension $p$.
--
--   **Formalization Note** The supremum is stated as "for every $\beta \in \mathcal B_{p',R}$". $s$ is any integer with $s > 1$ (the paper's standing convention, p. 5) and $R \ge 1$ (from Assumptions 1–2). The probability is an upper bound on the failure set.
-- source:
--   Liu, Ye & Lee, High-dimensional learning under approximate sparsity with applications to nonsmooth estimation and regularized neural networks, arXiv:1903.00616v2, p. ec20, Proposition 3

import Mathlib
import Definitions.Def_ApproxSparseHDSL_ExcessRisk_Model

open MeasureTheory ProbabilityTheory

namespace ApproxSparseHDSL.ExcessRisk

/-- Proposition 3, p. ec20: uniform deviation of the empirical risk over the sparse box
`B_{p′,R} = {β : ‖β‖∞ ≤ R, ‖β‖₀ ≤ p′}`, for `ϵ ∈ (0, 1]` and `p′ > s`. -/
theorem proposition_3 (c : ℝ) (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    ∃ ct : ℝ, 0 < ct ∧
    ∀ {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
      (P : Measure Ω) (μ : Measure E) (p n : ℕ) (Z : Fin n → Ω → E)
      (L : (Fin p → ℝ) → E → ℝ) (R σ : ℝ) (Cfn : E → ℝ) (sigL Cmu ε : ℝ) (s p' : ℕ),
      IIDSample P μ Z L → 1 ≤ R →
      Assumption3 P μ Z L R σ → Assumption4 P μ Z L R Cfn sigL Cmu →
      Bernstein12 P μ Z L R σ c → BernsteinC P μ Z Cfn sigL c →
      0 < ε → ε ≤ 1 → 1 < s → s < p' →
      P {ω | ¬ ∀ β : Fin p → ℝ, InBox R β → l0 β ≤ p' →
          |empRisk L (sample Z ω) β - popRisk μ L β| ≤
            σ / Real.sqrt n * Real.sqrt (2 * p' / c * zeta1 p R sigL Cmu ε)
              + σ / n * (2 * p' / c) * zeta1 p R sigL Cmu ε + ε}
        ≤ ENNReal.ofReal (2 * Real.exp (-(p' * zeta1 p R sigL Cmu ε))
            + 2 * Real.exp (-(ct * n))) := by sorry

end ApproxSparseHDSL.ExcessRisk
