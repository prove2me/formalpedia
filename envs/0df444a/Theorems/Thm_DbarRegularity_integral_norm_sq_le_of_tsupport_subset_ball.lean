-- Prove2me | Theorems.Thm_DbarRegularity_integral_norm_sq_le_of_tsupport_subset_ball
-- name    : DbarRegularity.integral_norm_sq_le_of_tsupport_subset_ball
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T23:00:09.871123+00:00
-- url     : https://prove2.me/theorems/a0f04560-5187-4e64-bd78-d1e20d8e96a2
-- title:
--   A one-dimensional L² Poincaré inequality with constant 4R²
-- statement:
--   Let $E$ be a real Banach space, $R\in\mathbb{R}$, and let $g:\mathbb{R}\to E$ be continuously differentiable with $\operatorname{supp} g\subseteq(-R,R)$ (closed support). Then
--   $$\int_{\mathbb{R}}\|g(x)\|^2\,dx\le 4R^2\int_{\mathbb{R}}\|g'(x)\|^2\,dx .$$
--   This is a one-dimensional $L^2$ Poincaré inequality for functions vanishing outside a bounded interval, with an explicit constant.
--
--   **Formalization Note** `ContDiff ℝ 1 g` is $C^1$ smoothness, `deriv g` is $g'$, and "support in $(-R,R)$" is `tsupport g ⊆ ball 0 R` (for $R\le 0$ this forces $g=0$). The integrals are Bochner integrals with respect to Lebesgue measure on $\mathbb{R}$.
-- source:
--   C. Abbas, H. Hofer, Holomorphic Curves and Global Questions in Contact Geometry, Birkhäuser Advanced Texts Basler Lehrbücher, Birkhäuser (2019), https://doi.org/10.1007/978-3-030-11803-7, § 4.2, p. 101

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace DbarRegularity

open MeasureTheory Metric Set

/-- One-dimensional L² Poincaré inequality: a `C¹` map `g : ℝ → E` with support in `(-R, R)`
satisfies `∫ ‖g‖² ≤ 4R² ∫ ‖g'‖²`. -/
theorem integral_norm_sq_le_of_tsupport_subset_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (R : ℝ) (g : ℝ → E) (hg : ContDiff ℝ 1 g)
    (hsupp : tsupport g ⊆ ball 0 R) :
    ∫ x, ‖g x‖ ^ 2 ≤ 4 * R ^ 2 * ∫ x, ‖deriv g x‖ ^ 2 := by sorry

end DbarRegularity
