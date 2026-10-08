-- Prove2me | Theorems.Thm_AdamDyn_Rates_eq_7_12
-- name    : AdamDyn.Rates.eq_7_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:44.684981+00:00
-- url     : https://prove2.me/theorems/58e3d4e2-9c22-4886-8bc2-237cb81837af
-- title:
--   §7.4 i), (7.12) — upper bound on $w_\delta(t)$ by the four residual terms
-- statement:
--   Let $F$, $S$, $a$, $b$, $\varepsilon$ satisfy the hypotheses of Theorem 3.2 without the condition on $F(\mathcal S)$ ($F$ is $C^1$ with locally Lipschitz gradient and coercive; $S$ is locally Lipschitz and coordinatewise positive; $a,b>0$, $b\le 4a$, $\varepsilon>0$). For a global solution $z(t)=(x(t),m(t),v(t))$ of the Adam ODE with initial condition $(x_0,0,0)$, let $w_\delta(t)=\tilde W_\delta(t,z(t))$ with $\tilde W_\delta$ as in (7.11).
--
--   Then for every $\delta>0$ there is a constant $c_1$ such that for every $x_0\in\mathbb R^d$, every global solution $z$ from $(x_0,0,0)$ and every $t\ge1$,
--
--   $$w_\delta(t)\ \le\ c_1\Big(|F(x(t))|+\|m(t)\|^2+\|\nabla F(x(t))\|^2+\|S(x(t))-v(t)\|^2\Big).$$
--
--   Together with (7.13) this compares $w_\delta$ with its own decay rate, which is the first half of the Łojasiewicz argument.
--
--   **Formalization Note** The constant $c_1$ may depend on $\delta$ (and on the data $a,\varepsilon$) but not on $x_0$ or the trajectory: it is quantified after $\delta$ and before $x_0$ and $z$, as in the paper ("depending on $\delta$", in contrast with the constants of (7.13), which depend on $x_0$).
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 20, §7.4 step i), Eq. (7.12)

import Mathlib
import Definitions.Def_AdamDyn_Rates_AdamField
import Definitions.Def_AdamDyn_Rates_Lyapunov

open Filter Topology

namespace AdamDyn.Rates

/-- Eq. (7.12), §7.4 step i) (Barakat–Bianchi, p. 20): for every `δ > 0` there is a constant `c1`
(depending on `δ`, not on the initial point or the trajectory) such that for every global solution
`z` from any `(x0, 0, 0)` and every `t ≥ 1`,
`w_δ(t) ≤ c1 (|F(x(t))| + ‖m(t)‖² + ‖∇F(x(t))‖² + ‖S(x(t)) − v(t)‖²)`, where
`w_δ(t) = W̃_δ(t, z(t))` (7.11). -/
theorem eq_7_12 {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (S : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a b ε : ℝ)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (hcoer : Tendsto F (cocompact (EuclideanSpace ℝ (Fin d))) atTop)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε) :
    ∀ δ > 0, ∃ c1 : ℝ, ∀ (x0 : EuclideanSpace ℝ (Fin d))
      (z : ℝ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)),
      IsGlobalSolution F S a b ε x0 z → ∀ t ≥ 1,
      wδ F S a b ε δ z t ≤
        c1 * (|F (z t).1| + ‖(z t).2.1‖ ^ 2 + ‖gradient F (z t).1‖ ^ 2 +
          ‖S (z t).1 - (z t).2.2‖ ^ 2) := by sorry

end AdamDyn.Rates
