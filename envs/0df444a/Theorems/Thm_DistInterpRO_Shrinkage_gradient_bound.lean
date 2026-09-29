-- Prove2me | Theorems.Thm_DistInterpRO_Shrinkage_gradient_bound
-- name    : DistInterpRO.Shrinkage.gradient_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:52:25.750406+00:00
-- url     : https://prove2.me/theorems/c341d592-91ab-4573-943b-d623c806d4d3
-- title:
--   §4.2, proof of Theorem 4.1 — a Hessian bound h makes the gradient h-Lipschitz; ‖g_v(x₀ + βx₁) − g_v(x₀ + αβ′x₁)‖ ≤ hD
-- statement:
--   Let $f(v,\cdot):\mathbb{R}^m\to\mathbb{R}$ be twice differentiable with $-hI\preceq H_v(x)\preceq hI$ for all $x$, where $h\ge0$ and $H_v(x)$ is the Hessian, and let $g_v$ be the gradient. Then:
--
--   1. $g_v$ is $h$-Lipschitz: $\|g_v(a)-g_v(b)\|_2\le h\|a-b\|_2$ for all $a,b$.
--   2. For every compact $\Delta\subseteq\mathbb{R}^m$ with $D=\max_{x\in\Delta}\|x\|_2$, every $\alpha\in(0,1)$, every $x_0$, $x_1\in\Delta$ and $\beta,\beta'\in[0,1]$,
--   $$\|g_v(x_0+\beta x_1)-g_v(x_0+\alpha\beta'x_1)\|\le h\|\beta x_1-\alpha\beta'x_1\|\le h\|x_1\|\le hD.$$
--
--   This is the second step of the proof of Theorem 4.1; it compares the gradients at the two mean-value points of the previous step.
--
--   **Formalization Note** The gradient is represented by `fderiv ℝ (f v) y`, a continuous linear functional whose operator norm equals the Euclidean norm of the gradient vector. The Hessian hypothesis is the quadratic-form bound $|D^2f(v,\cdot)(x)[y,y]|\le h\|y\|^2$ from the definition `HasBoundedHessian`; passing to the operator-norm bound on $D^2f$ uses the symmetry of the second derivative.
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 105, §4.2, proof of Theorem 4.1, third display

import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

/-- §4.2, proof of Theorem 4.1 (p. 105), third display: under the Hessian bound
`−hI ⪯ H_v ⪯ hI`, the gradient `g_v` is `h`-Lipschitz, and in particular
`‖g_v(x₀ + βx₁) − g_v(x₀ + αβ′x₁)‖ ≤ h‖βx₁ − αβ′x₁‖ ≤ h‖x₁‖ ≤ hD`
for `β, β′ ∈ [0, 1]`, `α ∈ (0, 1)`, `x₁ ∈ Δ`, `D = max_{x ∈ Δ} ‖x‖₂`. -/
theorem gradient_bound {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ) (v : V)
    (h : ℝ) (hh : 0 ≤ h) (hf : HasBoundedHessian (f v) h) :
    (∀ a b : EuclideanSpace ℝ (Fin m),
        ‖fderiv ℝ (f v) a - fderiv ℝ (f v) b‖ ≤ h * ‖a - b‖) ∧
    ∀ (Δ : Set (EuclideanSpace ℝ (Fin m))), IsCompact Δ →
      ∀ (α : ℝ), 0 < α → α < 1 →
      ∀ (x₀ x₁ : EuclideanSpace ℝ (Fin m)), x₁ ∈ Δ →
      ∀ β ∈ Set.Icc (0 : ℝ) 1, ∀ β' ∈ Set.Icc (0 : ℝ) 1,
        ‖fderiv ℝ (f v) (x₀ + β • x₁) - fderiv ℝ (f v) (x₀ + (α * β') • x₁)‖ ≤
            h * ‖β • x₁ - (α * β') • x₁‖ ∧
          h * ‖β • x₁ - (α * β') • x₁‖ ≤ h * ‖x₁‖ ∧
          h * ‖x₁‖ ≤ h * devRadius Δ := by sorry

end DistInterpRO.Shrinkage
