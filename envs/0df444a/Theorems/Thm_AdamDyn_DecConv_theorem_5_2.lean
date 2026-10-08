-- Prove2me | Theorems.Thm_AdamDyn_DecConv_theorem_5_2
-- name    : AdamDyn.DecConv.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:49.847134+00:00
-- url     : https://prove2.me/theorems/26de098b-7d48-4957-97fe-e9a571e29a20
-- title:
--   Theorem 5.2 — decreasing-step Adam converges almost surely to the critical points of $F$
-- statement:
--   Let $(\Omega, \mathcal F, \mathbb P)$ be a probability space, $\xi$ a random variable with law $\mu$ on $\Xi$, $f$ an integrand with gradient $\nabla f$, and $F$, $S$, $\mathcal S$ as in (2.2). Let $\varepsilon > 0$ and let $(\gamma_n, \alpha_n, \beta_n)$ satisfy Assumption 5.1 with constants $0 < b < 4a$, with moreover $\alpha_1 < 1$ and $\beta_1 < 1$. Assume Assumption 2.2, Assumption 2.3 ($F$ coercive), Assumption 2.4 ($S(x) > 0$ coordinatewise for all $x$), Assumption 4.1 (the samples $\xi_1, \xi_2, \dots$ are iid with law $\mu$) and Assumption 4.2 i) with $p = 4$. Let $z_n = (x_n, m_n, v_n)$ be the iterates of Algorithm 5.1 from $(x_0, 0, 0)$, and assume that, with probability one, the sequence $(z_n)$ is bounded. Assume finally that $F(\mathcal S)$ has an empty interior in $\mathbb R$. Then, with probability one,
--   $$ \lim_{n\to\infty} d(x_n, \mathcal S) = 0, \qquad \lim_{n\to\infty} m_n = 0, \qquad \lim_{n\to\infty} \big(S(x_n) - v_n\big) = 0 . $$
--   If moreover $\mathcal S$ is finite or countable, then with probability one there exists $x^* \in \mathcal S$ such that
--   $$ \lim_{n\to\infty} (x_n, m_n, v_n) = (x^*, 0, S(x^*)) . $$
--
--   This is the paper's almost-sure convergence theorem for Adam with decreasing stepsizes $\gamma_n$ and momentum parameters $1 - \alpha_n \sim a\gamma_n$, $1 - \beta_n \sim b\gamma_n$: under the condition $b < 4a$ the iterates approach the critical points of the objective, the momentum vanishes, and the second-moment estimate tracks $S(x_n)$.
--
--   **Formalization Note** Algorithm 5.1 divides by $r_n$ and $\bar r_n$; Assumption 5.1 iii) allows $\alpha_1 = 1$, in which case $r_1 = 0$. The hypotheses $\alpha_1 < 1$, $\beta_1 < 1$, implicit on the page, make all $r_n, \bar r_n$ positive; $\varepsilon > 0$ is likewise implicit. "Finite or countable" is `Set.Countable`. $d(x, \mathcal S)$ is `Metric.infDist`, which is $0$ for an empty set; here $\mathcal S$ is nonempty because $F$ is coercive and continuously differentiable, hence has a minimiser. The boundedness hypothesis is almost sure, not uniform in $\omega$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 8, Theorem 5.2 (with Algorithm 5.1 and Assumption 5.1, p. 8)

import Mathlib
import Definitions.Def_AdamDyn_DecConv_Algorithm
import Definitions.Def_AdamDyn_DecConv_StochasticModel

open MeasureTheory Filter Topology

namespace AdamDyn.DecConv

/-- Theorem 5.2 (Barakat & Bianchi, arXiv:1810.02263v4, p. 8). Let Assumptions 2.2 to 2.4, 4.1
and 5.1 hold, and Assumption 4.2 i) with `p = 4`. Assume that `F(𝒮)` has an empty interior and
that the sequence `((x_n, m_n, v_n) : n ∈ ℕ)` given by Algorithm 5.1 is bounded with probability
one. Then, w.p.1, `d(x_n, 𝒮) → 0`, `m_n → 0` and `S(x_n) − v_n → 0`. If moreover `𝒮` is finite or
countable, then w.p.1 there exists `x* ∈ 𝒮` with `(x_n, m_n, v_n) → (x*, 0, S(x*))`.
`F` and `S` are given by (2.2); `𝒮 = ∇F⁻¹({0})`. The hypotheses `α_1 < 1`, `β_1 < 1` make the
bias-correction divisors `r_n`, `r̄_n` of Algorithm 5.1 positive. -/
theorem theorem_5_2 {d : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : AdamDyn.WellPosed.Vec d → Ξ → ℝ) (gf : AdamDyn.WellPosed.Vec d → Ξ → AdamDyn.WellPosed.Vec d) (ξ : ℕ → Ω → Ξ)
    (γ α β : ℕ → ℝ) (a b ε : ℝ) (x0 : AdamDyn.WellPosed.Vec d)
    (hε : 0 < ε)
    (h22 : Assumption22 μ f gf)
    (h23 : Tendsto (AdamDyn.ConstStep.objective μ f) (cocompact (AdamDyn.WellPosed.Vec d)) atTop)
    (h24 : ∀ x i, 0 < AdamDyn.ConstStep.sqGradMean μ gf x i)
    (h41 : Assumption41 P μ ξ)
    (h51 : Assumption51 γ α β a b)
    (h42 : Assumption42i μ gf 4)
    (hα1 : α 1 < 1) (hβ1 : β 1 < 1)
    (hint : interior (AdamDyn.ConstStep.objective μ f '' criticalSet (AdamDyn.ConstStep.objective μ f)) = ∅)
    (hbdd : ∀ᵐ ω ∂P, Bornology.IsBounded (Set.range fun n => adamIter gf γ α β ε x0 ξ n ω)) :
    (∀ᵐ ω ∂P,
      Tendsto (fun n => Metric.infDist (adamIter gf γ α β ε x0 ξ n ω).1
          (criticalSet (AdamDyn.ConstStep.objective μ f))) atTop (𝓝 0) ∧
        Tendsto (fun n => (adamIter gf γ α β ε x0 ξ n ω).2.1) atTop (𝓝 0) ∧
        Tendsto (fun n => AdamDyn.ConstStep.sqGradMean μ gf (adamIter gf γ α β ε x0 ξ n ω).1 -
          (adamIter gf γ α β ε x0 ξ n ω).2.2) atTop (𝓝 0)) ∧
    ((criticalSet (AdamDyn.ConstStep.objective μ f)).Countable →
      ∀ᵐ ω ∂P, ∃ xs ∈ criticalSet (AdamDyn.ConstStep.objective μ f),
        Tendsto (fun n => adamIter gf γ α β ε x0 ξ n ω) atTop
          (𝓝 (xs, 0, AdamDyn.ConstStep.sqGradMean μ gf xs))) := by sorry

end AdamDyn.DecConv
