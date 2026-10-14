-- Prove2me | Theorems.Thm_DbarRegularity_eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball
-- name    : DbarRegularity.eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T23:39:47.888156+00:00
-- url     : https://prove2.me/theorems/4ad64a17-ac40-4fb4-be49-6ac5adf5049d
-- title:
--   An L^p Poincaré inequality on a disc in the real direction
-- statement:
--   Write $z=s+it$ for $z\in\mathbb{C}$ and $\varphi_s=\partial\varphi/\partial s$. Let $E$ be a real Banach space, $R\in\mathbb{R}$, $p\in[1,\infty)$ real, and let $\varphi:\mathbb{C}\to E$ be continuously differentiable with $\operatorname{supp}\varphi\subseteq B_R(0)$ (closed support inside the open disc). Then
--   $$\|\varphi\|_{L^p(\mathbb{C})}\le 2R\,\|\varphi_s\|_{L^p(\mathbb{C})},$$
--   with respect to Lebesgue measure on $\mathbb{C}$. This is an $L^p$ Poincaré inequality on the disc that uses only the derivative in the real direction, with a constant independent of $p$.
--
--   **Formalization Note** `ContDiff ℝ 1 φ` is $C^1$ smoothness over $\mathbb{R}$, $\varphi_s$ is `fderiv ℝ φ z 1`, and "support in $B_R(0)$" is `tsupport φ ⊆ ball 0 R` (for $R\le 0$ this forces $\varphi=0$). The norms are `eLpNorm _ (ENNReal.ofReal p) volume`, valued in $[0,\infty]$, and $2R$ enters as `ENNReal.ofReal (2 * R)`.
-- source:
--   C. Abbas, H. Hofer, Holomorphic Curves and Global Questions in Contact Geometry, Birkhäuser Advanced Texts Basler Lehrbücher, Birkhäuser (2019), https://doi.org/10.1007/978-3-030-11803-7, § 4.2, p. 102

import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.RealDeriv

namespace DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal

/-- `L^p` Poincaré inequality in the real direction on the plane: for real `p ≥ 1`, a `C¹` map
`φ : ℂ → E` with support in the disc `B_R(0)` satisfies `‖φ‖_{L^p} ≤ 2R ‖φ_s‖_{L^p}`, where
`φ_s = fderiv ℝ φ z 1`. -/
theorem eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (R p : ℝ) (hp : 1 ≤ p)
    (φ : ℂ → E) (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ ball 0 R) :
    eLpNorm φ (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (2 * R) * eLpNorm (fun z => fderiv ℝ φ z 1) (ENNReal.ofReal p) volume := by sorry

end DbarRegularity
