-- Prove2me | Theorems.Thm_DbarRegularity_integral_norm_dbar_sq
-- name    : DbarRegularity.integral_norm_dbar_sq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T22:20:30.915216+00:00
-- url     : https://prove2.me/theorems/04faade2-1d85-4774-999d-0bc5908a5e57
-- title:
--   The L² norm of the Cauchy–Riemann operator equals the L² norm of the gradient for compactly supported maps
-- statement:
--   Write $z=s+it$ for $z\in\mathbb{C}$, $\varphi_s=\partial\varphi/\partial s$, $\varphi_t=\partial\varphi/\partial t$ and $\bar\partial\varphi=\varphi_s+i\varphi_t$. $\mathbb{C}^n$ carries the Hermitian norm, and $\|\cdot\|_{L^p}$ is the $L^p$ norm on $\mathbb{C}$ with respect to Lebesgue measure. For every smooth compactly supported map $\varphi:\mathbb{C}\to\mathbb{C}^n$,
--   $$\|\bar\partial\varphi\|_{L^2(\mathbb{C})}^2=\|\varphi_s\|_{L^2(\mathbb{C})}^2+\|\varphi_t\|_{L^2(\mathbb{C})}^2 .$$
--
--   **Formalization Note** `ContDiff ℝ ∞ φ` is $C^\infty$ smoothness over $\mathbb{R}$ (not analyticity). $\varphi_s$ and $\varphi_t$ are `fderiv ℝ φ z 1` and `fderiv ℝ φ z Complex.I`, and $\bar\partial\varphi$ is `dbar φ`. $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`. Each squared $L^2$ norm is its own Bochner integral `∫ z, ‖·‖ ^ 2`; the first integral on the right is parenthesized so that the two integrals are added, not nested. This statement replaces `DbarRegularity.dbar_l2_identity`, whose right-hand side lacked these parentheses and therefore read $\int_{\mathbb{C}}\big(\|\varphi_s\|^2+\mathrm{const}\big)$.
-- source:
--   C. Abbas, H. Hofer, Holomorphic Curves and Global Questions in Contact Geometry, Birkhäuser Advanced Texts Basler Lehrbücher, Birkhäuser (2019), https://doi.org/10.1007/978-3-030-11803-7, § 4.2, formula (4.4), p. 100

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

/-- Abbas–Hofer, *Holomorphic Curves and Global Questions in Contact Geometry*, § 4.2, formula (4.4)
(p. 100): for a smooth compactly supported `φ : ℂ → ℂⁿ`,
`‖∂̄φ‖²_{L²(ℂ)} = ‖φ_s‖²_{L²(ℂ)} + ‖φ_t‖²_{L²(ℂ)}`, where `z = s + i t`. -/
theorem integral_norm_dbar_sq {n : ℕ} (φ : ℂ → EuclideanSpace ℂ (Fin n)) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∫ z, ‖dbar φ z‖ ^ 2 = (∫ z, ‖fderiv ℝ φ z 1‖ ^ 2) + ∫ z, ‖fderiv ℝ φ z Complex.I‖ ^ 2 := by sorry

end DbarRegularity
