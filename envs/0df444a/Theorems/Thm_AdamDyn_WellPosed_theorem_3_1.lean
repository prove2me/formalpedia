-- Prove2me | Theorems.Thm_AdamDyn_WellPosed_theorem_3_1
-- name    : AdamDyn.WellPosed.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:57.587101+00:00
-- url     : https://prove2.me/theorems/72891a46-363d-4682-b612-f42d3a1f2918
-- title:
--   Theorem 3.1 — the continuous-time Adam ODE has a unique global solution from $(x_0,0,0)$, and it is bounded
-- statement:
--   Let $a > 0$, $\varepsilon > 0$ and $0 < b \le 4a$. Let $F : \mathbb R^d \to \mathbb R$ be continuously differentiable with locally Lipschitz gradient and coercive ($F(x) \to +\infty$ as $\|x\| \to \infty$), and let $S : \mathbb R^d \to \mathbb R^d$ be locally Lipschitz with $S(x) > 0$ coordinatewise for every $x$. Consider the continuous-time Adam equation
--   $$\dot z(t) = h(t, z(t)),\qquad h(t,(x,m,v)) = \left( -\frac{(1-e^{-at})^{-1} m}{\varepsilon + \sqrt{(1-e^{-bt})^{-1} v}},\ a(\nabla F(x) - m),\ b(S(x) - v) \right),$$
--   on $\mathcal Z_+ = \mathbb R^d \times \mathbb R^d \times [0,+\infty)^d$ (operations coordinatewise), and fix $x_0 \in \mathbb R^d$. Then there exists a unique global solution $z : [0,+\infty) \to \mathcal Z_+$ with initial condition $(x_0,0,0)$ — continuous on $[0,+\infty)$, continuously differentiable on $(0,+\infty)$, satisfying the equation for every $t > 0$ — and its range $z([0,+\infty))$ is a bounded subset of $\mathcal Z_+$.
--
--   In the paper, $F(x) = \mathbb E f(x,\xi)$ and $S(x) = \mathbb E(\nabla f(x,\xi)^{\odot 2})$ are built from a stochastic objective satisfying Assumption 2.2, and $a, b$ are the limits in Assumption 2.5. Under Assumption 2.2 these $F$ and $S$ satisfy the hypotheses above (p. 3), and §7 of the paper proves the result for any $F$, $S$ satisfying them (Assumptions 7.1–7.2), so the statement here is the paper's Theorem 3.1 in the generality of its proof. It establishes that the continuous-time limit of Adam is well posed, which is the starting point for all the convergence results on the Adam dynamics.
--
--   **Formalization Note.** Uniqueness is agreement on $[0,+\infty)$ of any two global solutions, since a map $\mathbb R \to \mathcal Z$ is unconstrained for $t < 0$. The field is evaluated only at $t > 0$; boundedness is with respect to Lean's product norm on $\mathcal Z$, which is equivalent to the Euclidean norm of $\mathbb R^{3d}$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 5, Theorem 3.1 (proof: §7.2, pp. 13–17)

import Mathlib
import Definitions.Def_AdamDyn_WellPosed_adamField

open Filter

namespace AdamDyn.WellPosed

/-- Theorem 3.1 (p. 5), in the generality of §7 (F, S abstract, Assumptions 7.1–7.2, 2.3–2.5).
There exists a unique global solution `z : [0, +∞) → 𝒵₊` to `(ODE)` with initial condition
`(x0, 0, 0)`; moreover `z([0, +∞))` is a bounded subset of `𝒵₊`. -/
theorem theorem_3_1 {d : ℕ} (a b ε : ℝ) (F : Vec d → ℝ) (S : Vec d → Vec d)
    (ha : 0 < a) (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hcoer : Tendsto F (cocompact (Vec d)) atTop)
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (x0 : Vec d) :
    (∃ z : ℝ → State d, IsGlobalSolution a b ε F S x0 z ∧
        Bornology.IsBounded (z '' Set.Ici 0)) ∧
    ∀ z z' : ℝ → State d, IsGlobalSolution a b ε F S x0 z → IsGlobalSolution a b ε F S x0 z' →
      Set.EqOn z z' (Set.Ici 0) := by sorry

end AdamDyn.WellPosed
