-- Prove2me | Theorems.Thm_AdamDyn_ODEConv_theorem_3_2
-- name    : AdamDyn.ODEConv.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:17.291749+00:00
-- url     : https://prove2.me/theorems/32420280-bb09-4a81-ad1d-d0131f1c6c6c
-- title:
--   Theorem 3.2 — the continuous-time Adam trajectory converges to the critical points of $F$
-- statement:
--   Let $F : \mathbb R^d \to \mathbb R$ be continuously differentiable with locally Lipschitz gradient and coercive, and let $S : \mathbb R^d \to \mathbb R^d$ be locally Lipschitz with $S(x) > 0$ coordinatewise for every $x$. Let $0 < b \le 4a$ and $\varepsilon > 0$. Write $\mathcal S = \nabla F^{-1}(\{0\})$ for the set of critical points of $F$ and assume that $F(\mathcal S)$ has an empty interior in $\mathbb R$.
--
--   Let $z : t \mapsto (x(t), m(t), v(t))$ be a global solution to
--   $$ \dot z(t) = h(t, z(t)), \qquad h(t, z) = \Big( -\frac{(1-e^{-at})^{-1} m}{\varepsilon + \sqrt{(1-e^{-bt})^{-1} v}},\ a(\nabla F(x) - m),\ b(S(x) - v)\Big), $$
--   with initial condition $(x_0, 0, 0)$. Then $\mathcal S$ is non-empty and
--   $$ \lim_{t\to\infty} d(x(t), \mathcal S) = 0, \qquad \lim_{t\to\infty} m(t) = 0, \qquad \lim_{t\to\infty} \big(S(x(t)) - v(t)\big) = 0. $$
--
--   This is the main convergence theorem for the continuous-time version of Adam: the ODE obtained as the small-step limit of Adam drives the iterate to the critical set of the objective, the momentum to zero and the second-moment estimate to $S$ along the trajectory.
--
--   **Formalization Note** The paper states the theorem under Assumptions 2.2–2.5, with $F(x) = \mathbb E f(x,\xi)$ and $S(x) = \mathbb E \nabla f(x,\xi)^{\odot 2}$; §7 proves it for any $F$, $S$ satisfying Assumptions 7.1–7.2 (p. 11), which the $F$, $S$ of (2.2) do under Assumption 2.2 (p. 3). The Lean statement is in that generality and so implies the printed theorem. The theorem is stated for every global solution (one exists and is unique by Theorem 3.1). $d(x, \mathcal S)$ is `Metric.infDist`; non-emptiness of $\mathcal S$ is part of the conclusion, so the first limit is not vacuous.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 5, Theorem 3.2; proof in §7.3, pp. 17–20

import Mathlib
import Definitions.Def_AdamDyn_ODEConv_AdamField

open Filter Topology

namespace AdamDyn.ODEConv

/-- Theorem 3.2 (Convergence) (Barakat & Bianchi, arXiv:1810.02263v4, p. 5), in the generality
of §7 (Assumptions 7.1, 7.2, p. 11, which the `F`, `S` of (2.2) satisfy under Assumption 2.2):
`F` is `C¹` with locally Lipschitz gradient and coercive (Ass. 2.3), `S` is locally Lipschitz
with `S(x) > 0` (Ass. 2.4), `0 < b ≤ 4a` (Ass. 2.5), `ε > 0`. Assume that `F(𝒮)` has an empty
interior, where `𝒮 = ∇F⁻¹({0})`. Let `z = (x, m, v)` be a global solution to (ODE) with initial
condition `(x0, 0, 0)`. Then `𝒮` is non-empty and `d(x(t), 𝒮) → 0`, `m(t) → 0`,
`S(x(t)) − v(t) → 0` as `t → ∞`. -/
theorem theorem_3_2 {d : ℕ} (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (hcoer : Tendsto F (cocompact (AdamDyn.WellPosed.Vec d)) atTop)
    (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (hint : interior (F '' {x | gradient F x = 0}) = ∅)
    (x0 : AdamDyn.WellPosed.Vec d) (z : ℝ → AdamDyn.WellPosed.State d) (hz : IsGlobalSolution a b ε F S x0 z) :
    {x | gradient F x = 0}.Nonempty ∧
      Tendsto (fun t => Metric.infDist (z t).1 {x | gradient F x = 0}) atTop (𝓝 0) ∧
      Tendsto (fun t => (z t).2.1) atTop (𝓝 0) ∧
      Tendsto (fun t => S (z t).1 - (z t).2.2) atTop (𝓝 0) := by sorry

end AdamDyn.ODEConv
