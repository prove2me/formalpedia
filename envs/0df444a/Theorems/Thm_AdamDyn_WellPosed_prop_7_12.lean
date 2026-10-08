-- Prove2me | Theorems.Thm_AdamDyn_WellPosed_prop_7_12
-- name    : AdamDyn.WellPosed.prop_7_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:01.095116+00:00
-- url     : https://prove2.me/theorems/9e42b6df-8baf-4883-a0f3-e46bf2cd22b7
-- title:
--   Proposition 7.12 — the Adam equation (ODE) has exactly one global solution from every $(x_0,0,0)$
-- statement:
--   Let $a, b, \varepsilon > 0$ with $b \le 4a$. Let $F : \mathbb R^d \to \mathbb R$ be continuously differentiable with locally Lipschitz gradient (Assumption 7.1) and coercive (Assumption 2.3), and let $S : \mathbb R^d \to \mathbb R^d$ be locally Lipschitz (Assumption 7.2) with $S(x) > 0$ coordinatewise (Assumption 2.4). Then for every $z_0 \in \mathcal Z_0$ the set $Z^0_\infty(z_0)$ is a singleton: there is a global solution of $\dot z(t) = h(t, z(t))$ on $[0,+\infty)$ with initial condition $z_0$, and any two such solutions coincide on $[0,+\infty)$.
--
--   Uniqueness fails for general initial conditions and cannot be obtained from the Cauchy–Lipschitz theorem, since $h(t,\cdot)$ is not locally Lipschitz at $v = 0$ and $h(\cdot, z)$ is singular at $t = 0$.
--
--   **Formalization Note.** Solutions are maps $\mathbb R \to \mathcal Z$ constrained only on $[0,+\infty)$, so "singleton" is stated as existence together with agreement on $[0,+\infty)$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 16, Proposition 7.12

import Mathlib
import Definitions.Def_AdamDyn_WellPosed_adamField

open scoped NNReal
open Filter

namespace AdamDyn.WellPosed

/-- Proposition 7.12 (p. 16). Under Assumptions 2.3, 2.4, 7.1, 7.2 and `b ≤ 4a` (with the standing
`a, b > 0`): for every `z0 ∈ 𝒵₀`, `Z^0_∞(z0)` is a singleton — there is a global solution of
`(ODE)` from `z0`, and any two agree on `[0, +∞)`. -/
theorem prop_7_12 {d : ℕ} (a b ε : ℝ) (F : Vec d → ℝ) (S : Vec d → Vec d)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hcoer : Tendsto F (cocompact (Vec d)) atTop)
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (z0 : State d) (hz0 : z0 ∈ Zzero) :
    (∃ z : ℝ → State d, IsSolutionOn a b ε F S ((0 : ℝ≥0) : WithTop ℝ≥0) ⊤ z0 z) ∧
    ∀ z z' : ℝ → State d,
      IsSolutionOn a b ε F S ((0 : ℝ≥0) : WithTop ℝ≥0) ⊤ z0 z →
      IsSolutionOn a b ε F S ((0 : ℝ≥0) : WithTop ℝ≥0) ⊤ z0 z' →
        Set.EqOn z z' (Set.Ici 0) := by sorry

end AdamDyn.WellPosed
