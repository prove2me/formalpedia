-- Prove2me | Theorems.Thm_FastCLO_ERM_theorem_6
-- name    : FastCLO.ERM.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:23:07.983532+00:00
-- url     : https://prove2.me/theorems/3c6fad71-da5f-4aed-bd2e-363e79c15e5c
-- title:
--   Theorem 6 — under the noise condition, ERM over a class of Natarajan dimension η containing π* has regret ≤ C(α,γ) B (η log(|Z∠|+1) log(n+1)/n)^{(1+α)/(2+α)}
-- statement:
--   Let $\alpha, \gamma \ge 0$. There is a constant $C(\alpha, \gamma)$, depending only on $\alpha$ and $\gamma$, with the following property.
--
--   Let $\mathcal Z = \{z : Az \le b\} \subseteq \mathbb R^d$ be a nonempty polytope with $\sup_{z \in \mathcal Z}\|z\| \le B$ and extreme points $\mathcal Z^\angle$. Let $(X, Y) \in \mathbb R^p \times \mathbb R^d$ have $\|Y\| \le 1$, regression function $f^*(x) = \mathbb E[Y \mid X = x]$ and optimal sets $\mathcal Z^*(x) = \arg\min_{z \in \mathcal Z} f^*(x)^\top z$. Suppose
--
--   1. the noise condition (Assumption 2) holds with $\alpha, \gamma$: $\mathbb P_X(0 < \Delta(X) \le \delta) \le (\gamma\delta/B)^\alpha$ for all $\delta > 0$;
--   2. $\mathbb P(|\mathcal Z^*(X)| > 1) = 0$;
--   3. the policy class $\Pi \subseteq [\mathbb R^p \to \mathcal Z^\angle]$ has Natarajan dimension at most $\eta$;
--   4. $\pi^* \in \Pi$: some member of $\Pi$ is optimal for almost every $x$.
--
--   Let $\hat\pi^{\mathrm{ERM}}_\Pi$ choose, from $n \ge 1$ i.i.d. draws of $(X, Y)$, a policy in $\Pi$ minimizing the empirical cost $\frac1n\sum_i Y_i^\top\pi(X_i)$. Then
--
--   $$\mathrm{Regret}(\hat\pi^{\mathrm{ERM}}_\Pi) \le C(\alpha, \gamma)\,B\left(\frac{\eta\log(|\mathcal Z^\angle| + 1)\log(n + 1)}{n}\right)^{\frac{1+\alpha}{2+\alpha}}.$$
--
--   For $\alpha > 0$ this is faster than the noise-independent rate $n^{-1/2}$, and Theorem 7 of the paper shows the dependence on $n$ and $\eta$ cannot be improved beyond logarithmic factors.
--
--   **Formalization Note** The constant is chosen before the dimensions, the polytope, the distribution, the class, $\eta$ and $n$. The distribution of $(X, Y)$ is given by the law of $X$ and the conditional law of $Y$; the regret is measured against the optimal value $\min_{z \in \mathcal Z} f^*(X)^\top z$, which equals $f^*(X)^\top\pi^*(X)$. Every selection from the empirical argmin counts as ERM (the paper's tie-breaking order is not encoded), and the ERM rule is assumed measurable jointly in the data and the feature so that the regret is a genuine expectation.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, Theorem 6, §3.1, p. 9

import Mathlib
import Definitions.Def_FastCLO_ERM_ERM
import Definitions.Def_FastCLO_ERM_NatShatters
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace FastCLO.ERM

/-- **Theorem 6** (Hu, Kallus, Mao, *Fast Rates for Contextual Linear Optimization*,
arXiv:2011.03030v3, §3.1, p. 9). Suppose Assumption 2 holds, `P(|Z*(X)| > 1) = 0`,
`Π ⊆ [ℝ^p → Z∠]` has Natarajan dimension at most `η`, and `π* ∈ Π`. Then, for a constant
`C(α, γ)` depending only on `α, γ`,
`Regret(π̂^ERM_Π) ≤ C(α, γ) B (η log(|Z∠| + 1) log(n + 1)/n)^{(1+α)/(2+α)}`.

Formalization Note: `C` is chosen before the dimensions, the polytope, the distribution, the
policy class `PC`, `η` and `n`. The distribution is `(μ, κ)` (law of `X`, conditional law of `Y`);
the regret is measured against the optimal value. `π* ∈ Π` is read as: some member of `Π` is optimal
at almost every `x`. The ERM algorithm is any selection from the empirical argmin over the whole
class (tie-breaking not encoded), assumed jointly measurable in the data and the feature so that the
regret is a genuine integral. `1 ≤ n` because the page divides by `n`. -/
theorem theorem_6 (α γ : ℝ) (hα : 0 ≤ α) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (p d : ℕ) (P : Polytope d) (I : Instance p d) (PC : Set (Vec p → Vec d))
      (η n : ℕ) (alg : (Fin n → Vec p × Vec d) → Vec p → Vec d),
      1 ≤ n →
      NoiseCond P I α γ →
      (∀ᵐ x ∂I.μ, (Zstar P I x).Subsingleton) →
      (∀ π ∈ PC, IsPolicy P π) →
      ¬ NatShatters PC (η + 1) →
      (∃ πs ∈ PC, ∀ᵐ x ∂I.μ, πs x ∈ Zstar P I x) →
      (∀ D, IsERM PC D (alg D)) →
      Measurable (Function.uncurry alg) →
      regret P I n alg ≤ C * P.B *
        ((η : ℝ) * Real.log ((P.ext.ncard : ℝ) + 1) * Real.log ((n : ℝ) + 1) / n)
          ^ ((1 + α) / (2 + α)) := by sorry

end FastCLO.ERM
