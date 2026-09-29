-- Prove2me | Theorems.Thm_DistInterpRO_Shrinkage_min_sandwich
-- name    : DistInterpRO.Shrinkage.min_sandwich
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:53:21.208252+00:00
-- url     : https://prove2.me/theorems/c867f637-9de6-4267-9e94-f7c530ae5a72
-- title:
--   §4.2, proof of Theorem 4.1 — min over αΔ within αD²h of (1 − α)f(v, x₀) + α·min over Δ
-- statement:
--   Let $\Delta\subseteq\mathbb{R}^m$ be compact with $0\in\Delta$ and $D=\max_{x\in\Delta}\|x\|_2$, let $\alpha\in(0,1)$, $x_0\in\mathbb{R}^m$, and let $f(v,\cdot)$ be twice differentiable with $-hI\preceq H_v(x)\preceq hI$ for all $x$, where $h\ge0$. Then
--   $$(1-\alpha)f(v,x_0)+\alpha\min_{x_\delta\in\Delta}f(v,x_0+x_\delta)-\alpha D^2h\le\min_{x_\delta'\in\alpha\Delta}f(v,x_0+x_\delta')\le(1-\alpha)f(v,x_0)+\alpha\min_{x_\delta\in\Delta}f(v,x_0+x_\delta)+\alpha D^2h.$$
--
--   This passes the pointwise sandwich to the minima over $\Delta$ and $\alpha\Delta=\{\alpha x : x\in\Delta\}$.
--
--   **Formalization Note** Both minima are written as real infima over the subtypes of $\Delta$ and $\alpha\Delta$; they are attained because both sets are compact and nonempty and $f(v,\cdot)$ is continuous. Compactness and $0\in\Delta$ are the section's implicit standing hypotheses made explicit ($0\in\Delta$ is used here only for nonemptiness).
-- source:
--   Xu, Caramanis and Mannor, A Distributional Interpretation of Robust Optimization, Math. Oper. Res. 37(1) (2012), p. 105, §4.2, proof of Theorem 4.1, display after "Since this holds for all x₁ ∈ Δ"

import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

/-- §4.2, proof of Theorem 4.1 (p. 105), display after "Since this holds for all x₁ ∈ Δ":
`(1−α)f(v, x₀) + α min_{x_δ∈Δ} f(v, x₀+x_δ) − αD²h ≤ min_{x′_δ∈αΔ} f(v, x₀+x′_δ)
  ≤ (1−α)f(v, x₀) + α min_{x_δ∈Δ} f(v, x₀+x_δ) + αD²h`.
The minima are written as infima over the compact sets `Δ` and `αΔ`; they are attained. -/
theorem min_sandwich {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ) (v : V)
    (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m))) (hΔc : IsCompact Δ)
    (hΔ0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ Δ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h : ℝ) (hh : 0 ≤ h) (hf : HasBoundedHessian (f v) h) :
    (1 - α) * f v x₀ + α * (⨅ x : Δ, f v (x₀ + x)) - α * devRadius Δ ^ 2 * h ≤
        (⨅ x : (α • Δ : Set (EuclideanSpace ℝ (Fin m))), f v (x₀ + x)) ∧
      (⨅ x : (α • Δ : Set (EuclideanSpace ℝ (Fin m))), f v (x₀ + x)) ≤
        (1 - α) * f v x₀ + α * (⨅ x : Δ, f v (x₀ + x)) + α * devRadius Δ ^ 2 * h := by sorry

end DistInterpRO.Shrinkage
