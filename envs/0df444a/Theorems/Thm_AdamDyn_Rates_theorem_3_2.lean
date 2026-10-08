-- Prove2me | Theorems.Thm_AdamDyn_Rates_theorem_3_2
-- name    : AdamDyn.Rates.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:02:27.857441+00:00
-- url     : https://prove2.me/theorems/15d63ffa-3af3-4cfc-8604-d637df7b2eff
-- title:
--   Theorem 3.2 — the Adam ODE trajectory converges to the critical set of $F$
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R$ be continuously differentiable with locally Lipschitz gradient and coercive ($F(x)\to+\infty$ as $\|x\|\to\infty$), and let $S:\mathbb R^d\to\mathbb R^d$ be locally Lipschitz with $S(x)>0$ coordinatewise for every $x$. Let $a>0$, $b>0$ with $b\le 4a$, and $\varepsilon>0$. Write $\mathcal S=\{x:\nabla F(x)=0\}$ and assume that $F(\mathcal S)$ has empty interior in $\mathbb R$.
--
--   Let $z(t)=(x(t),m(t),v(t))$ be a global solution of the Adam ODE $\dot z=h(t,z)$ with initial condition $(x_0,0,0)$. Then $\mathcal S$ is nonempty and
--
--   $$\lim_{t\to\infty} d(x(t),\mathcal S)=0,\qquad \lim_{t\to\infty} m(t)=0,\qquad \lim_{t\to\infty}\big(S(x(t))-v(t)\big)=0 .$$
--
--   In the convergence-rate proof this theorem identifies the limit of $V(t,z(t))$ with the limit of $F(x(t))$, gives $w_\delta(t)\to\ell$, and places the limit set of the trajectory inside the critical set.
--
--   **Formalization Note** The statement is in the generality of §7 of the paper (any $F$, $S$ with the properties above), which contains the paper's Theorem 3.2, where $F(x)=\mathbb E f(x,\xi)$ and $S(x)=\mathbb E\,\nabla f(x,\xi)^{\odot2}$ satisfy these properties under Assumptions 2.2–2.4. The statement is made for every global solution; there is exactly one (Theorem 3.1). The nonemptiness of $\mathcal S$ is part of the conclusion, so the distance $d(x(t),\mathcal S)$ is the distance to a nonempty set.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 5, Theorem 3.2 (proved in §7.3 under Assumptions 2.3, 2.4, 7.1, 7.2, p. 11)

import Mathlib
import Definitions.Def_AdamDyn_Rates_Lojasiewicz
import Definitions.Def_AdamDyn_Rates_AdamField

open Filter Topology

namespace AdamDyn.Rates

/-- Theorem 3.2 (Convergence, Barakat–Bianchi, p. 5), in the generality of §7 (Assumptions 7.1,
7.2, 2.3, 2.4, and `a, b > 0`, `b ≤ 4a`, `ε > 0`). If `F(𝒮)` has an empty interior and `z` is a
global solution of (ODE) from `(x0, 0, 0)`, then `𝒮` is nonempty, `d(x(t), 𝒮) → 0`, `m(t) → 0` and
`S(x(t)) − v(t) → 0` as `t → ∞`. -/
theorem theorem_3_2 {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (S : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a b ε : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d))
    (z : ℝ → EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (hcoer : Tendsto F (cocompact (EuclideanSpace ℝ (Fin d))) atTop)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (hint : interior (F '' critSet F) = ∅)
    (hz : IsGlobalSolution F S a b ε x0 z) :
    (critSet F).Nonempty ∧
      Tendsto (fun t => Metric.infDist (z t).1 (critSet F)) atTop (𝓝 0) ∧
      Tendsto (fun t => (z t).2.1) atTop (𝓝 0) ∧
      Tendsto (fun t => S (z t).1 - (z t).2.2) atTop (𝓝 0) := by sorry

end AdamDyn.Rates
