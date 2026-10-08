-- Prove2me | Theorems.Thm_AdamDyn_ConstStep_proposition_7_12
-- name    : AdamDyn.ConstStep.proposition_7_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:39.316986+00:00
-- url     : https://prove2.me/theorems/736cc861-bb2e-4601-8fa9-c4ad0eff04e8
-- title:
--   Proposition 7.12 — $Z^0_\infty((x_0,0,0))$ is a singleton: the Adam ODE has a unique global solution
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R$ be continuously differentiable and coercive with locally Lipschitz gradient, let $S:\mathbb R^d\to\mathbb R^d$ be locally Lipschitz with $S(x)>0$ coordinatewise (Assumptions 2.3, 2.4, 7.1, 7.2), and let $\varepsilon>0$ and $0<b\le4a$. For every $x_0\in\mathbb R^d$ the set $Z^0_\infty((x_0,0,0))$ of global solutions of
--
--   $$
--   \dot z(t) = h(t,z(t)),\qquad z(0)=(x_0,0,0),
--   $$
--
--   is a singleton: a global solution exists, and any two global solutions coincide on $[0,+\infty)$.
--
--   Uniqueness is what identifies every limit point of the interpolated Adam processes with the same deterministic trajectory.
--
--   **Formalization Note** Global solutions are maps $\mathbb R\to\mathcal Z$ (values at negative times are irrelevant), so uniqueness is agreement on $[0,+\infty)$. The statement is posed for any $F$, $S$ satisfying the hypotheses above, the generality of §7; positivity of $a$ and $b$ comes from Assumption 2.5.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 16, Proposition 7.12

import Mathlib
import Definitions.Def_AdamDyn_ConstStep_adamField

open Filter Topology
open scoped ENNReal

namespace AdamDyn.ConstStep

/-- Proposition 7.12 (p. 16), for any `F`, `S` satisfying Assumptions 2.3, 2.4, 7.1, 7.2 and
`0 < b ≤ 4a`: for `z0 = (x0, 0, 0) ∈ 𝒵₀`, `Z^0_∞(z0)` is a singleton — there is a global
solution of (ODE) with initial condition `z0`, and any two agree on `[0, +∞)`. -/
theorem proposition_7_12 {d : ℕ} (F : E d → ℝ) (S : E d → E d) (a b ε : ℝ) (x0 : E d)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (hcoer : Tendsto F (cocompact (E d)) atTop)
    (ha : 0 < a) (hb : 0 < b) (hab : b ≤ 4 * a) (hε : 0 < ε) :
    ∃ z : ℝ → Z d, IsSolutionOn a b ε F S 0 ⊤ (x0, 0, 0) z ∧
      ∀ z' : ℝ → Z d, IsSolutionOn a b ε F S 0 ⊤ (x0, 0, 0) z' → Set.EqOn z' z (Set.Ici 0) := by sorry

end AdamDyn.ConstStep
