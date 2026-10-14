-- Prove2me | Theorems.Thm_DbarRegularity_dbar_l2_bound
-- name    : DbarRegularity.dbar_l2_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T22:20:30.775+00:00
-- url     : https://prove2.me/theorems/f8d60017-9e43-43b6-88cf-d5ffebdb379d
-- title:
--   The L² estimate for the Cauchy–Riemann operator on a disc
-- statement:
--   Write $z=s+it$ for $z\in\mathbb{C}$, $\varphi_s=\partial\varphi/\partial s$, $\varphi_t=\partial\varphi/\partial t$ and $\bar\partial\varphi=\varphi_s+i\varphi_t$. $\mathbb{C}^n$ carries the Hermitian norm, and $\|\cdot\|_{L^p}$ is the $L^p$ norm on $\mathbb{C}$ with respect to Lebesgue measure. Let $R>0$ and let $\varphi:\mathbb{C}\to\mathbb{C}^n$ be smooth with compact support in the open disc $B_R(0)$. Then
--   $$\|\varphi_s\|_{L^2}^2+\|\varphi_t\|_{L^2}^2+\|\varphi\|_{L^2}^2\le(4R^2+1)\,\|\bar\partial\varphi\|_{L^2}^2 .$$
--
--   **Formalization Note** `ContDiff ℝ ∞ φ` is $C^\infty$ smoothness over $\mathbb{R}$ (not analyticity). $\varphi_s$ and $\varphi_t$ are `fderiv ℝ φ z 1` and `fderiv ℝ φ z Complex.I`, and $\bar\partial\varphi$ is `dbar φ`. $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`. "Compact support in $B_R(0)$" is `tsupport φ ⊆ ball 0 R` (for $R\le 0$ this forces $\varphi=0$). Each squared $L^2$ norm is its own Bochner integral `∫ z, ‖·‖ ^ 2`; the three integrals on the left are parenthesized so that they are added, not nested. This statement replaces `DbarRegularity.dbar_l2_estimate`, whose left-hand side lacked these parentheses.
-- source:
--   C. Abbas, H. Hofer, Holomorphic Curves and Global Questions in Contact Geometry, Birkhäuser Advanced Texts Basler Lehrbücher, Birkhäuser (2019), https://doi.org/10.1007/978-3-030-11803-7, § 4.2, Theorem 4.2.1, p. 101

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

/-- Abbas–Hofer, *Holomorphic Curves and Global Questions in Contact Geometry*, § 4.2, Theorem 4.2.1
(p. 101): for a smooth `φ : ℂ → ℂⁿ` with compact support in the disc `B_R(0)`,
`‖φ_s‖²_{L²} + ‖φ_t‖²_{L²} + ‖φ‖²_{L²} ≤ (4R² + 1) ‖∂̄φ‖²_{L²}`, where `z = s + i t`. -/
theorem dbar_l2_bound {n : ℕ} (R : ℝ) (φ : ℂ → EuclideanSpace ℂ (Fin n))
    (hφ : ContDiff ℝ ∞ φ) (hsupp : tsupport φ ⊆ ball 0 R) :
    (∫ z, ‖fderiv ℝ φ z 1‖ ^ 2) + (∫ z, ‖fderiv ℝ φ z Complex.I‖ ^ 2) + (∫ z, ‖φ z‖ ^ 2)
      ≤ (4 * R ^ 2 + 1) * ∫ z, ‖dbar φ z‖ ^ 2 := by sorry

end DbarRegularity
