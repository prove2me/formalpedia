-- Prove2me | Theorems.Thm_ExpConeIPM_Curvature_gradient_formula
-- name    : ExpConeIPM.Curvature.gradient_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:40.936091+00:00
-- url     : https://prove2.me/theorems/94e9c34f-a8fd-4df7-82d1-04b989597906
-- title:
--   A.1 — first-order derivatives of the exponential-cone barrier
-- statement:
--   Let $F$ be the exponential-cone barrier (2), $\psi(x) = x_2\log(x_1/x_2) - x_3$, $g = -\log\psi$ and $h(x) = -\log x_1 - \log x_2$, so $F = g + h$. For every $x \in \operatorname{int}(K_{\exp})$,
--
--   $$
--   \psi'(x) = \bigl(x_2/x_1,\ \log(x_1/x_2) - 1,\ -1\bigr), \qquad h'(x) = -\bigl(1/x_1,\ 1/x_2,\ 0\bigr),
--   $$
--
--   $$
--   g'(x) = -\frac{\psi'(x)}{\psi(x)}, \qquad F'(x) = g'(x) + h'(x).
--   $$
--
--   These closed forms are what the interior-point method evaluates for the gradient of the barrier, and the starting point for the second- and third-order formulas of Appendix A.
--
--   **Formalization Note** Gradients are `gradient` on `EuclideanSpace ℝ (Fin 3)`, and vectors are written `!₂[·, ·, ·]`; the paper's $(x_1, x_2, x_3)$ are `(x 0, x 1, x 2)`. The hypothesis $x \in \operatorname{int}(K_{\exp})$ is the paper's standing domain of the barrier; outside it the logarithms are junk.
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), p. 367, Appendix A.1

import Mathlib
import Definitions.Def_ExpConeIPM_Curvature_ExpCone
import Definitions.Def_ExpConeIPM_Curvature_NegativeCurvature

open scoped InnerProductSpace

namespace ExpConeIPM.Curvature

/-- **A.1, p. 367 — first-order derivatives.** For `x ∈ int(Kexp)`, with
`ψ(x) = x₂ log(x₁/x₂) − x₃`, `g = −log ψ`, `h = −log x₁ − log x₂` (so `F = g + h`):
`ψ'(x) = (x₂/x₁, log(x₁/x₂) − 1, −1)`, `h'(x) = −(1/x₁, 1/x₂, 0)`, `g'(x) = −ψ'(x)/ψ(x)` and
`F'(x) = g'(x) + h'(x)`. -/
theorem gradient_formula (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ interior Kexp) :
    gradient psi x = !₂[x 1 / x 0, Real.log (x 0 / x 1) - 1, -1] ∧
      gradient h x = -!₂[1 / x 0, 1 / x 1, 0] ∧
      gradient g x = -(1 / psi x) • gradient psi x ∧
      gradient barrier x = gradient g x + gradient h x := by sorry

end ExpConeIPM.Curvature
