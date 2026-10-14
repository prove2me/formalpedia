-- Prove2me | Theorems.Thm_DbarRegularity_integral_norm_sq_le_integral_norm_fderiv_one_sq
-- name    : DbarRegularity.integral_norm_sq_le_integral_norm_fderiv_one_sq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T23:08:20.701313+00:00
-- url     : https://prove2.me/theorems/1908ef9a-09f9-4209-9ce5-723aaf412e03
-- title:
--   An L² Poincaré inequality on a disc in the real direction
-- statement:
--   Write $z=s+it$ for $z\in\mathbb{C}$ and $\varphi_s=\partial\varphi/\partial s$. Let $E$ be a real Banach space, $R\in\mathbb{R}$, and let $\varphi:\mathbb{C}\to E$ be continuously differentiable with $\operatorname{supp}\varphi\subseteq B_R(0)$ (closed support inside the open disc). Then
--   $$\int_{\mathbb{C}}\|\varphi(z)\|^2\,dz\le 4R^2\int_{\mathbb{C}}\|\varphi_s(z)\|^2\,dz ,$$
--   with respect to Lebesgue measure on $\mathbb{C}$. This is an $L^2$ Poincaré inequality on the disc that uses only the derivative in the real direction.
--
--   **Formalization Note** `ContDiff ℝ 1 φ` is $C^1$ smoothness over $\mathbb{R}$, $\varphi_s$ is `fderiv ℝ φ z 1`, and "support in $B_R(0)$" is `tsupport φ ⊆ ball 0 R` (for $R\le 0$ this forces $\varphi=0$). The integrals are Bochner integrals.
-- source:
--   C. Abbas, H. Hofer, Holomorphic Curves and Global Questions in Contact Geometry, Birkhäuser Advanced Texts Basler Lehrbücher, Birkhäuser (2019), https://doi.org/10.1007/978-3-030-11803-7, § 4.2, p. 101

import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.RealDeriv

namespace DbarRegularity

open MeasureTheory Metric Set

/-- L² Poincaré inequality in the real direction on the plane: a `C¹` map `φ : ℂ → E` with support
in the disc `B_R(0)` satisfies `∫ ‖φ‖² ≤ 4R² ∫ ‖φ_s‖²`, where `φ_s = fderiv ℝ φ z 1`. -/
theorem integral_norm_sq_le_integral_norm_fderiv_one_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (R : ℝ) (φ : ℂ → E) (hφ : ContDiff ℝ 1 φ)
    (hsupp : tsupport φ ⊆ ball 0 R) :
    ∫ z, ‖φ z‖ ^ 2 ≤ 4 * R ^ 2 * ∫ z, ‖fderiv ℝ φ z 1‖ ^ 2 := by sorry

end DbarRegularity
