-- Prove2me | Theorems.Thm_FastCLO_ETO_theorem_8
-- name    : FastCLO.ETO.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:17:00.773651+00:00
-- url     : https://prove2.me/theorems/d7cbff02-576b-4c1c-8ac0-75923703ea0b
-- title:
--   Theorem 8 — under the noise condition, a plug-in policy with pointwise sub-Gaussian estimation error at rate aₙ has regret ≤ C(α,γ) B aₙ^{−(1+α)/2}
-- statement:
--   Let $\mathcal Z = \{z : Az \le b\} \subseteq \mathbb R^d$ be a nonempty polytope with $\|z\| \le B$ on $\mathcal Z$ and extreme points $\mathcal Z^\angle$. Let $(X, Y)$ have feature law $\mathbb P_X$ on $\mathbb R^p$ and bounded costs $\|Y\| \le 1$, with $f^*(x) = \mathbb E[Y \mid X = x]$ and gap $\Delta$. From $n$ i.i.d. observations $\mathcal D$ an estimate $\hat f = \hat f_{\mathcal D}$ of $f^*$ is formed, and the estimate-then-optimize policy $\pi_{\hat f}$ chooses, at every $x$, an extreme point minimizing $\hat f(x)^\top z$ over $\mathcal Z$.
--
--   Fix $\alpha, \gamma \ge 0$ and constants $C_1, C_2 > 0$. There is a constant $C$, depending only on $\alpha, \gamma, C_1, C_2$, such that the following holds for every polytope, every distribution, every $n$, every $a_n > 0$ and every estimator. If
--
--   1. the noise condition (Assumption 2) holds: $\mathbb P_X(0 < \Delta(X) \le \delta) \le (\gamma\delta/B)^\alpha$ for all $\delta > 0$, and
--   2. for every $\delta > 0$ and almost every $x$, $\mathbb P_{\mathcal D}\bigl(\|\hat f(x) - f^*(x)\| \ge \delta\bigr) \le C_1 \exp(-C_2 a_n \delta^2)$,
--
--   then
--
--   $$\mathrm{Regret}(\pi_{\hat f}) \le C\, B\, a_n^{-\frac{1+\alpha}{2}}.$$
--
--   With $a_n$ of order $n$ up to a logarithmic factor, as for well-specified least squares, the rate $n^{-(1+\alpha)/2}$ is, up to logarithms, faster than the rate $n^{-(1+\alpha)/(2+\alpha)}$ that no method relying only on a policy class of finite Natarajan dimension can beat (Theorem 7 of the paper): estimate-then-optimize can outperform integrated methods.
--
--   **Formalization Note** The paper writes $C(\alpha, \gamma)$ and calls $C_1, C_2$ universal constants; here $C$ is chosen after $\alpha, \gamma, C_1, C_2$ and before everything else, which is that reading. The distribution is given as the law of $X$ together with the conditional law of $Y$ given $X$. Plug-in policies are any selection from the argmin with values in $\mathcal Z^\angle$ (the paper's consistent tie-breaking is not required, which makes the statement stronger). The estimator and the policy are assumed jointly measurable in the data and the feature, so that the regret is a genuine integral; the paper leaves this implicit. Positivity of $C_1, C_2$ and of $a_n$ is the paper's implicit convention.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, Theorem 8, p. 9 (proof in Appendix A.5, p. 30)

import Mathlib
import Definitions.Def_FastCLO_ETO_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace FastCLO.ETO

/-- **Theorem 8** (Hu, Kallus, Mao, *Fast Rates for Contextual Linear Optimization*,
arXiv:2011.03030v3, §3.2, p. 9). "Suppose Assumption 2 holds and, for universal constants C₁, C₂
and a sequence aₙ, f̂ satisfies that, for any δ > 0 and almost all x,
P(‖f̂(x) − f*(x)‖ ≥ δ) ≤ C₁ exp(−C₂ aₙ δ²). Then, for a constant C(α, γ) depending only on α, γ,
Regret(π_f̂) ≤ C(α, γ) B aₙ^{−(1+α)/2}."

Formalization Note: `C` is chosen after `α, γ` and the universal constants `C₁, C₂`, and before
the dimensions, the polytope, the distribution, the sample size `n`, the estimator, the policy and
`aₙ` (written `a > 0`, needed for the real power). The distribution is `(μ, κ)` (law of `X`,
conditional law of `Y`), `f*` is the conditional mean, and the regret is measured against the
optimal value. The estimator `fhat D` and the plug-in policy `pihat D` are computed from the data
`D` (any selection from the argmin with values in `Z∠`; tie-breaking not encoded), assumed jointly
measurable in `(D, x)` so that the regret is a genuine integral. The tail condition bounds, for every
`δ > 0` and almost every fixed `x`, the probability over the data. `C₁, C₂ > 0` is the page's
implicit positivity of the constants. -/
theorem theorem_8 (α γ C₁ C₂ : ℝ) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) :
    ∃ C : ℝ, ∀ (p d : ℕ) (P : Polytope d) (I : Instance p d) (n : ℕ)
      (fhat pihat : (Fin n → FastCLO.ERM.Vec p × FastCLO.ERM.Vec d) → FastCLO.ERM.Vec p → FastCLO.ERM.Vec d) (a : ℝ),
      0 < a →
      NoiseCond P I α γ →
      (∀ D, IsPlugIn P (fhat D) (pihat D)) →
      Measurable (Function.uncurry fhat) →
      Measurable (Function.uncurry pihat) →
      (∀ δ > 0, ∀ᵐ x ∂I.μ,
        I.sample n {D | δ ≤ ‖fhat D x - I.fstar x‖} ≤
          ENNReal.ofReal (C₁ * Real.exp (-C₂ * a * δ ^ 2))) →
      regret P I n pihat ≤ C * P.B * a ^ (-(1 + α) / 2) := by sorry

end FastCLO.ETO
