-- Prove2me | Theorems.Thm_DistInterpRO_Shrinkage_mean_value_step
-- name    : DistInterpRO.Shrinkage.mean_value_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:51:56.451341+00:00
-- url     : https://prove2.me/theorems/7bb96ac1-1c1d-4ec5-a57c-64a382083101
-- title:
--   §4.2, proof of Theorem 4.1 — the mean-value step f(v, x₀ + x₁) = f(v, x₀) + g_v(x₀ + βx₁)x₁
-- statement:
--   Let $f(v,\cdot):\mathbb{R}^m\to\mathbb{R}$ be differentiable, and write $g_v(y)$ for its gradient at $y$ (acting on a vector $z$ as $g_v(y)z$). For all $x_0,x_1\in\mathbb{R}^m$ there exists $\beta\in[0,1]$ such that
--   $$f(v,x_0+x_1)=f(v,x_0)+g_v(x_0+\beta x_1)\,x_1 .$$
--
--   This is the first step of the proof of Theorem 4.1: it expresses the change of $f(v,\cdot)$ along the segment from $x_0$ to $x_0+x_1$ through one gradient evaluation. The proof applies it twice, to $x_1$ and to $x_1'=\alpha x_1$.
--
--   **Formalization Note** $g_v(y)z$ is `fderiv ℝ (f v) y z`. The page assumes twice differentiability; this step uses only differentiability.
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 105, §4.2, proof of Theorem 4.1, first display

import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

/-- §4.2, proof of Theorem 4.1 (p. 105), first display: the mean-value step
`f(v, x₀ + x₁) = f(v, x₀) + g_v(x₀ + βx₁)x₁` for some `β ∈ [0, 1]`, where
`g_v(y)z = fderiv ℝ (f v) y z`. -/
theorem mean_value_step {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ) (v : V)
    (hf : Differentiable ℝ (f v)) (x₀ x₁ : EuclideanSpace ℝ (Fin m)) :
    ∃ β ∈ Set.Icc (0 : ℝ) 1, f v (x₀ + x₁) = f v x₀ + fderiv ℝ (f v) (x₀ + β • x₁) x₁ := by sorry

end DistInterpRO.Shrinkage
