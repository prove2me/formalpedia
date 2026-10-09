-- Prove2me | Theorems.Thm_FastCLO_ETO_iterated_bound
-- name    : FastCLO.ETO.iterated_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:17:08.380802+00:00
-- url     : https://prove2.me/theorems/5a6eb41e-f8e8-4ff7-82aa-157dbeff69f3
-- title:
--   Proof of Theorem 8, after iterating expectations — Regret(π_f̂) ≤ Bγ^α(2δ)^{α+1} + Bγ^αC₁δ^{α+1} Σ_r 2^{(r+1)(α+1)} exp(−C₂aₙ(2^{r−1}δ)²)
-- statement:
--   Let $\mathcal Z$ be a polytope with norm bound $B$ and fix an instance with feature law $\mathbb P_X$, regression function $f^*$ and gap $\Delta$. Let $\alpha, \gamma \ge 0$, $C_1, C_2 > 0$, $a_n > 0$ and a sample size $n$. Let $\hat f$ be an estimator and $\pi_{\hat f}$ a plug-in policy for it, as in the peeled bound, both jointly measurable in the data and the feature. Assume:
--
--   1. the noise condition (Assumption 2): $\mathbb P_X(0 < \Delta(X) \le t) \le (\gamma t/B)^\alpha$ for all $t > 0$;
--   2. the tail condition: for every $t > 0$ and $\mathbb P_X$-almost every $x$, $\mathbb P_{\mathcal D}\bigl(\|\hat f_{\mathcal D}(x) - f^*(x)\| \ge t\bigr) \le C_1 \exp(-C_2 a_n t^2)$.
--
--   Then for every $\delta > 0$,
--
--   $$\mathrm{Regret}(\pi_{\hat f}) \le B\gamma^\alpha (2\delta)^{\alpha+1} + B\gamma^\alpha C_1 \delta^{\alpha+1} \sum_{r=1}^\infty 2^{(r+1)(\alpha+1)} \exp\bigl(-C_2 a_n (2^{r-1}\delta)^2\bigr).$$
--
--   This is the last display of the proof of Theorem 8 before the choice $\delta = a_n^{-1/2}$, which turns the right-hand side into $C B a_n^{-(1+\alpha)/2}$ with a constant $C$ depending only on $\alpha, \gamma, C_1, C_2$.
--
--   **Formalization Note** The series is indexed from $0$ in Lean (the paper's $r$ is Lean's $r + 1$). Since $C_2 a_n \delta^2 > 0$ the series converges, so its real sum is the genuine sum. Joint measurability of the estimator and the policy is not stated in the paper; it makes the regret a genuine integral.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, proof of Theorem 8 (Appendix A.5), the display after "iterating expectations with respect to X", p. 30

import Mathlib
import Definitions.Def_FastCLO_ETO_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace FastCLO.ETO

/-- **Proof of Theorem 8, the bound after iterating expectations** (Hu, Kallus, Mao, *Fast Rates
for Contextual Linear Optimization*, arXiv:2011.03030v3, Appendix A.5, p. 30): under the hypotheses
of Theorem 8, for every `δ > 0`,
`Regret(π_f̂) ≤ Bγ^α(2δ)^{α+1} + Bγ^αC₁δ^{α+1} Σ_{r=1}^∞ 2^{(r+1)(α+1)} exp(−C₂aₙ(2^{r−1}δ)²)`.

Hypotheses: the noise condition (7) with exponents `α, γ ≥ 0`; `pihat D` is a plug-in policy for
the estimate `fhat D` computed from the data `D`; and for every `δ > 0` and almost every `x`, the
probability over the data that `‖f̂(x) − f*(x)‖ ≥ δ` is at most `C₁ exp(−C₂ a δ²)`.

Formalization Note: the page's `r ≥ 1` is re-indexed as `r + 1` with `r ≥ 0`. Because
`C₂ a δ² > 0`, the series converges, so the real `tsum` is the genuine sum. `a > 0` stands for the
page's `aₙ`, and `C₁, C₂ > 0` for its universal constants. Joint measurability of `fhat` and
`pihat` in `(D, x)` is assumed so that the regret is a genuine integral. -/
theorem iterated_bound {p d : ℕ} (P : Polytope d) (I : Instance p d) (n : ℕ)
    (α γ C₁ C₂ a : ℝ) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (ha : 0 < a)
    (fhat pihat : (Fin n → FastCLO.ERM.Vec p × FastCLO.ERM.Vec d) → FastCLO.ERM.Vec p → FastCLO.ERM.Vec d)
    (hnoise : NoiseCond P I α γ)
    (hplug : ∀ D, IsPlugIn P (fhat D) (pihat D))
    (hf : Measurable (Function.uncurry fhat)) (hpi : Measurable (Function.uncurry pihat))
    (htail : ∀ δ > 0, ∀ᵐ x ∂I.μ,
      I.sample n {D | δ ≤ ‖fhat D x - I.fstar x‖} ≤ ENNReal.ofReal (C₁ * Real.exp (-C₂ * a * δ ^ 2)))
    (δ : ℝ) (hδ : 0 < δ) :
    regret P I n pihat ≤
      P.B * γ ^ α * (2 * δ) ^ (α + 1) +
      P.B * γ ^ α * C₁ * δ ^ (α + 1) *
        ∑' r : ℕ, (2 : ℝ) ^ (((r : ℝ) + 2) * (α + 1)) * Real.exp (-C₂ * a * (2 ^ r * δ) ^ 2) := by sorry

end FastCLO.ETO
