-- Prove2me | Theorems.Thm_DbarRegularity_integral_norm_dbar_sq_of_innerProductSpace
-- name    : DbarRegularity.integral_norm_dbar_sq_of_innerProductSpace
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T22:20:01.991311+00:00
-- url     : https://prove2.me/theorems/23413903-709b-44dd-bc73-e3dafeb76714
-- title:
--   The L² norm of the Cauchy–Riemann operator for maps into a complex Hilbert space
-- statement:
--   Write $z=s+it$ for $z\in\mathbb{C}$, $\varphi_s=\partial\varphi/\partial s$, $\varphi_t=\partial\varphi/\partial t$ and $\bar\partial\varphi=\varphi_s+i\varphi_t$. Let $E$ be a complex Hilbert space. For every smooth compactly supported map $\varphi:\mathbb{C}\to E$,
--   $$\int_{\mathbb{C}}\|\bar\partial\varphi\|^2=\int_{\mathbb{C}}\|\varphi_s\|^2+\int_{\mathbb{C}}\|\varphi_t\|^2 ,$$
--   with respect to Lebesgue measure on $\mathbb{C}$. This is the identity $\|\bar\partial\varphi\|_{L^2}^2=\|\varphi_s\|_{L^2}^2+\|\varphi_t\|_{L^2}^2$ for an arbitrary Hilbert-space target.
--
--   **Formalization Note** `ContDiff ℝ ∞ φ` is $C^\infty$ smoothness over $\mathbb{R}$ (not analyticity). $\varphi_s$ and $\varphi_t$ are `fderiv ℝ φ z 1` and `fderiv ℝ φ z Complex.I`, and $\bar\partial\varphi$ is `dbar φ`. $E$ is a complete complex inner product space (`InnerProductSpace ℂ E`, `CompleteSpace E`). Each squared norm is its own Bochner integral `∫ z, ‖·‖ ^ 2`; the first integral on the right is parenthesized so that the two integrals are added, not nested.
-- source:
--   C. Abbas, H. Hofer, Holomorphic Curves and Global Questions in Contact Geometry, Birkhäuser Advanced Texts Basler Lehrbücher, Birkhäuser (2019), https://doi.org/10.1007/978-3-030-11803-7, § 4.2, formula (4.4), p. 100

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

namespace DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

/-- For a smooth compactly supported map `φ : ℂ → E` into a complex Hilbert space,
`‖∂̄φ‖²_{L²(ℂ)} = ‖φ_s‖²_{L²(ℂ)} + ‖φ_t‖²_{L²(ℂ)}`, where `z = s + i t`. -/
theorem integral_norm_dbar_sq_of_innerProductSpace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (φ : ℂ → E) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∫ z, ‖dbar φ z‖ ^ 2 = (∫ z, ‖fderiv ℝ φ z 1‖ ^ 2) + ∫ z, ‖fderiv ℝ φ z Complex.I‖ ^ 2 := by sorry

end DbarRegularity
