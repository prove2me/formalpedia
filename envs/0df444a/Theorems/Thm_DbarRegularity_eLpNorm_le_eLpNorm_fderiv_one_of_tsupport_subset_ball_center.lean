-- Prove2me | Theorems.Thm_DbarRegularity_eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball_center
-- name    : DbarRegularity.eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball_center
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-13T15:24:39.227116+00:00
-- url     : https://prove2.me/theorems/9a7dea23-0e67-40a3-82be-ac9b83754778
-- title:
--   An L^p Poincaré inequality on a disc with arbitrary centre in the real direction
-- statement:
--   Write $z=s+it$ for $z\in\mathbb{C}$ and $\varphi_s=\partial\varphi/\partial s$. Let $E$ be a real Banach space, $c\in\mathbb C$, $R\in\mathbb{R}$, $p\in[1,\infty)$ real, and let $\varphi:\mathbb{C}\to E$ be continuously differentiable with $\operatorname{supp}\varphi\subseteq B_R(c)$ (closed support inside the open disc of radius $R$ centred at $c$). Then
--   $$\|\varphi\|_{L^p(\mathbb{C})}\le 2R\,\|\varphi_s\|_{L^p(\mathbb{C})},$$
--   with respect to Lebesgue measure on $\mathbb{C}$. The constant does not depend on the centre $c$ or on $p$.
--
--   **Formalization Note** `ContDiff ℝ 1 φ` is $C^1$ smoothness over $\mathbb{R}$, $\varphi_s$ is `fderiv ℝ φ z 1`, and "support in $B_R(c)$" is `tsupport φ ⊆ ball c R` (for $R\le 0$ this forces $\varphi=0$). The norms are `eLpNorm _ (ENNReal.ofReal p) volume`, valued in $[0,\infty]$, and $2R$ enters as `ENNReal.ofReal (2 * R)`.
-- source:
--   C. Abbas, H. Hofer, Holomorphic Curves and Global Questions in Contact Geometry, Birkhäuser Advanced Texts Basler Lehrbücher, Birkhäuser (2019), https://doi.org/10.1007/978-3-030-11803-7, § 4.2, p. 102

import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.FDeriv.Const

namespace DbarRegularity

open MeasureTheory Metric

/-- `L^p` Poincaré inequality in the real direction on a disc `B_R(c)` with arbitrary centre:
`‖φ‖_{L^p} ≤ 2R ‖∂φ/∂s‖_{L^p}` for `C¹` maps `φ : ℂ → E` with support in `B_R(c)`. -/
theorem eLpNorm_le_eLpNorm_fderiv_one_of_tsupport_subset_ball_center {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (c : ℂ) (R p : ℝ) (hp : 1 ≤ p)
    (φ : ℂ → E) (hφ : ContDiff ℝ 1 φ) (hsupp : tsupport φ ⊆ ball c R) :
    eLpNorm φ (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (2 * R) * eLpNorm (fun z => fderiv ℝ φ z 1) (ENNReal.ofReal p) volume := by sorry

end DbarRegularity
