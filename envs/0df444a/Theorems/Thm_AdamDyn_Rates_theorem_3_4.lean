-- Prove2me | Theorems.Thm_AdamDyn_Rates_theorem_3_4
-- name    : AdamDyn.Rates.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:08.318274+00:00
-- url     : https://prove2.me/theorems/09fb34cb-87ea-4a9b-b189-e00673a1240f
-- title:
--   Theorem 3.4 — under the Łojasiewicz property the Adam ODE converges to one critical point at rate $t^{-\theta/(1-2\theta)}$
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R$ be continuously differentiable with locally Lipschitz gradient and coercive, and let $S:\mathbb R^d\to\mathbb R^d$ be locally Lipschitz with $S(x)>0$ coordinatewise. Let $a>0$, $b>0$ with $b\le4a$, and $\varepsilon>0$. Assume that $F$ has the Łojasiewicz property (every critical point has a Łojasiewicz exponent in $(0,\tfrac12]$, Assumption 3.3) and that $F(\mathcal S)$ has empty interior, where $\mathcal S=\{x:\nabla F(x)=0\}$. Let $z(t)=(x(t),m(t),v(t))$ be a global solution of the Adam ODE $\dot z=h(t,z)$ with initial condition $(x_0,0,0)$.
--
--   Then there exists $x^*\in\mathcal S$ such that $x(t)\to x^*$ as $t\to+\infty$. Moreover, if $\theta\in(0,\tfrac12]$ is a Łojasiewicz exponent of $F$ at $x^*$, then:
--
--   1. if $0<\theta<\tfrac12$, there is a constant $C>0$ such that for all $t>0$,
--   $$\|x(t)-x^*\|\ \le\ C\,t^{-\frac{\theta}{1-2\theta}};$$
--   2. if $\theta=\tfrac12$, there are constants $C>0$ and $\delta>0$ such that for all $t\ge0$,
--   $$\|x(t)-x^*\|\ \le\ C\,e^{-\delta t}.$$
--
--   The result upgrades convergence to the critical set (Theorem 3.2) to convergence of the whole trajectory to a single critical point, with an explicit rate determined by the local geometry of $F$ at the limit.
--
--   **Formalization Note** The statement is in the generality of §7 of the paper, which contains the paper's Theorem 3.4 for $F(x)=\mathbb E f(x,\xi)$, $S(x)=\mathbb E\nabla f(x,\xi)^{\odot2}$. The exponent $\theta$ is quantified after $x^*$ is chosen, and the constant $C$ (and $\delta$) after $\theta$; they may depend on $x_0$, the trajectory, $x^*$ and $\theta$. The polynomial bound is stated for $t>0$: at $t=0$ the paper's right-hand side is $+\infty$, while Lean's real power gives $0^{-r}=0$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 6, Theorem 3.4 (proof in §7.4, pp. 20–21)

import Mathlib
import Definitions.Def_AdamDyn_Rates_Lojasiewicz
import Definitions.Def_AdamDyn_Rates_AdamField

open Filter Topology

namespace AdamDyn.Rates

/-- Theorem 3.4 (Barakat–Bianchi, p. 6), in the generality of §7 (Assumptions 7.1, 7.2, 2.3, 2.4,
`a, b > 0`, `b ≤ 4a`, `ε > 0`) together with Assumption 3.3. If `F(𝒮)` has an empty interior and
`z = (x, m, v)` is a global solution of (ODE) from `(x0, 0, 0)`, then `x(t)` converges to some
`xstar ∈ 𝒮`. Moreover, if `θ ∈ (0, 1/2]` is a Łojasiewicz exponent of `F` at `xstar`, there is
`C > 0` with `‖x(t) − xstar‖ ≤ C t^{−θ/(1−2θ)}` for all `t > 0` when `θ < 1/2`, and
`‖x(t) − xstar‖ ≤ C e^{−δt}` for all `t ≥ 0`, for some `δ > 0`, when `θ = 1/2`. -/
theorem theorem_3_4 {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (S : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a b ε : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d))
    (z : ℝ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (hcoer : Tendsto F (cocompact (EuclideanSpace ℝ (Fin d))) atTop)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (hLoj : LojasiewiczProperty F)
    (hint : interior (F '' critSet F) = ∅)
    (hz : IsGlobalSolution F S a b ε x0 z) :
    ∃ xstar ∈ critSet F, Tendsto (fun t => (z t).1) atTop (𝓝 xstar) ∧
      ∀ θ ∈ Set.Ioc (0 : ℝ) (1 / 2), IsLojExponent F xstar θ →
        (θ < 1 / 2 → ∃ C > 0, ∀ t > 0,
          ‖(z t).1 - xstar‖ ≤ C * t ^ (-(θ / (1 - 2 * θ)))) ∧
        (θ = 1 / 2 → ∃ C > 0, ∃ δ > 0, ∀ t ≥ 0,
          ‖(z t).1 - xstar‖ ≤ C * Real.exp (-δ * t)) := by sorry

end AdamDyn.Rates
