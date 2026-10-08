-- Prove2me | Theorems.Thm_AdamDyn_WellPosed_lemma_7_3
-- name    : AdamDyn.WellPosed.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:35.069399+00:00
-- url     : https://prove2.me/theorems/7bfae68d-fa1d-4042-bb2e-884293bdb6c4
-- title:
--   Lemma 7.3 — solutions from $(x_0,0,0)$ are $C^1$ at $t=0$ with explicit initial derivatives
-- statement:
--   Let $a, b, \varepsilon > 0$. Let $F : \mathbb R^d \to \mathbb R$ be continuously differentiable with locally Lipschitz gradient (Assumption 7.1), and let $S : \mathbb R^d \to [0,+\infty)^d$ be locally Lipschitz (Assumption 7.2). Let $x_0 \in \mathbb R^d$, $T \in (0,+\infty]$, and let $z(t) = (x(t), m(t), v(t))$ be a solution of the Adam equation $\dot z(t) = h(t, z(t))$ on $[0,T)$ with initial condition $(x_0, 0, 0)$, i.e. $z \in Z^0_T((x_0,0,0))$. Then $z$ is continuously differentiable on $[0,T)$, and its right derivative at $0$ is
--   $$\dot x(0) = -\frac{\nabla F(x_0)}{\varepsilon + \sqrt{S(x_0)}}, \qquad \dot m(0) = a\,\nabla F(x_0), \qquad \dot v(0) = b\,S(x_0),$$
--   the quotient and the square root taken coordinatewise.
--
--   Although the vector field $h(t,\cdot)$ is singular as $t \downarrow 0$, solutions issued from the Adam initialization $(x_0, 0, 0)$ have a well-defined initial velocity; this is used in the uniqueness proof and in the cost-decrease estimate.
--
--   **Formalization Note.** Continuous differentiability on $[0,T)$ is `ContDiffOn ℝ 1` on that half-open interval (one-sided at $0$), and the initial derivative is a derivative within $[0,+\infty)$ at $0$. The constants $a, b, \varepsilon > 0$ are standing assumptions of the paper (Assumption 2.5 and Algorithm 2.1).
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 12, Lemma 7.3

import Mathlib
import Definitions.Def_AdamDyn_WellPosed_adamField

open scoped NNReal

namespace AdamDyn.WellPosed

/-- Lemma 7.3 (p. 12). Under Assumptions 7.1–7.2 (and the standing `a, b, ε > 0`), a solution of
`(ODE)` on `[0, T)` from `(x0, 0, 0)` is continuously differentiable on `[0, T)` (one-sided at 0),
with `ẋ(0) = −∇F(x0)/(ε + √S(x0))`, `ṁ(0) = a∇F(x0)`, `v̇(0) = bS(x0)`. -/
theorem lemma_7_3 {d : ℕ} (a b ε : ℝ) (F : Vec d → ℝ) (S : Vec d → Vec d)
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSnn : ∀ x i, 0 ≤ S x i)
    (x0 : Vec d) (T : WithTop ℝ) (hT : 0 < T) (z : ℝ → State d)
    (hz : IsSolutionOn a b ε F S ((0 : ℝ≥0) : WithTop ℝ≥0) T (x0, 0, 0) z) :
    ContDiffOn ℝ 1 z (timeIco T) ∧
      HasDerivWithinAt z
        (WithLp.toLp 2 (fun i => -(gradient F x0 i) / (ε + Real.sqrt (S x0 i))),
          a • gradient F x0, b • S x0) (Set.Ici 0) 0 := by sorry

end AdamDyn.WellPosed
