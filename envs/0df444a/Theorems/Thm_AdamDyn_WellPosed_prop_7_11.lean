-- Prove2me | Theorems.Thm_AdamDyn_WellPosed_prop_7_11
-- name    : AdamDyn.WellPosed.prop_7_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:48.340307+00:00
-- url     : https://prove2.me/theorems/a8eb74e0-8155-41de-9a12-61f64154b55c
-- title:
--   Proposition 7.11 — the Adam equation (ODE) has a global solution from every $(x_0,0,0)$
-- statement:
--   Let $a, \varepsilon > 0$ and $0 < b \le 4a$. Let $F : \mathbb R^d \to \mathbb R$ be continuously differentiable with locally Lipschitz gradient (Assumption 7.1) and coercive (Assumption 2.3), and let $S : \mathbb R^d \to \mathbb R^d$ be locally Lipschitz (Assumption 7.2) with $S(x) > 0$ coordinatewise (Assumption 2.4). Then for every $z_0 \in \mathcal Z_0$,
--   $$Z^0_\infty(z_0) \neq \emptyset,$$
--   that is, the continuous-time Adam equation $\dot z(t) = h(t, z(t))$ admits a global solution on $[0,+\infty)$ issued from $z_0$.
--
--   This is the existence half of Theorem 3.1; it is not a consequence of the Cauchy–Peano theorem, because $h(\cdot, z)$ is singular at $t = 0$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 15, Proposition 7.11

import Mathlib
import Definitions.Def_AdamDyn_WellPosed_adamField

open scoped NNReal
open Filter

namespace AdamDyn.WellPosed

/-- Proposition 7.11 (p. 15). Under Assumptions 2.3, 2.4, 7.1, 7.2 and `0 < b ≤ 4a`: for every
`z0 ∈ 𝒵₀`, `Z^0_∞(z0) ≠ ∅`, i.e. `(ODE)` admits a global solution issued from `z0`. -/
theorem prop_7_11 {d : ℕ} (a b ε : ℝ) (F : Vec d → ℝ) (S : Vec d → Vec d)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hcoer : Tendsto F (cocompact (Vec d)) atTop)
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (z0 : State d) (hz0 : z0 ∈ Zzero) :
    ∃ z : ℝ → State d, IsSolutionOn a b ε F S ((0 : ℝ≥0) : WithTop ℝ≥0) ⊤ z0 z := by sorry

end AdamDyn.WellPosed
