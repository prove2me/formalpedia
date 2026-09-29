-- Prove2me | Theorems.Thm_DistInterpRO_Shrinkage_pointwise_sandwich
-- name    : DistInterpRO.Shrinkage.pointwise_sandwich
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:52:50.909879+00:00
-- url     : https://prove2.me/theorems/f08269f9-984f-409b-a3cd-222eab9613c8
-- title:
--   §4.2, proof of Theorem 4.1 — pointwise sandwich for f(v, x₀ + αx₁) within αD²h
-- statement:
--   Let $\Delta\subseteq\mathbb{R}^m$ be compact with $D=\max_{x\in\Delta}\|x\|_2$, let $\alpha\in(0,1)$, $x_0\in\mathbb{R}^m$, and let $f(v,\cdot)$ be twice differentiable with $-hI\preceq H_v(x)\preceq hI$ for all $x$, where $h\ge0$. For every $x_1\in\Delta$ and $x_1'=\alpha x_1$,
--   $$(1-\alpha)f(v,x_0)+\alpha f(v,x_0+x_1)-\alpha D^2h\le f(v,x_0+x_1')\le(1-\alpha)f(v,x_0)+\alpha f(v,x_0+x_1)+\alpha D^2h.$$
--
--   The value at the shrunken deviation $\alpha x_1$ is thus, up to $\alpha D^2h$, the two-point average that puts weight $1-\alpha$ on the nominal value and $\alpha$ on the full deviation.
--
--   **Formalization Note** $D$ is `devRadius Δ` (a supremum, attained since $\Delta$ is compact and contains $x_1$). Compactness of $\Delta$ is an added hypothesis that makes $D$ the paper's maximum.
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 105, §4.2, proof of Theorem 4.1, display after "Thus,"

import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

/-- §4.2, proof of Theorem 4.1 (p. 105), display after "Thus,": for `x₁ ∈ Δ` and
`x′₁ = αx₁`,
`(1 − α)f(v, x₀) + αf(v, x₀ + x₁) − αD²h ≤ f(v, x₀ + x′₁)
  ≤ (1 − α)f(v, x₀) + αf(v, x₀ + x₁) + αD²h`. -/
theorem pointwise_sandwich {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ) (v : V)
    (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m))) (hΔc : IsCompact Δ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h : ℝ) (hh : 0 ≤ h) (hf : HasBoundedHessian (f v) h)
    (x₁ : EuclideanSpace ℝ (Fin m)) (hx₁ : x₁ ∈ Δ) :
    (1 - α) * f v x₀ + α * f v (x₀ + x₁) - α * devRadius Δ ^ 2 * h ≤ f v (x₀ + α • x₁) ∧
      f v (x₀ + α • x₁) ≤ (1 - α) * f v x₀ + α * f v (x₀ + x₁) + α * devRadius Δ ^ 2 * h := by sorry

end DistInterpRO.Shrinkage
