-- Prove2me | Theorems.Thm_DbarRegularity_dbar_lp_estimate
-- name    : DbarRegularity.dbar_lp_estimate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T21:55:28.84432+00:00
-- url     : https://prove2.me/theorems/081ad0cf-543c-43c9-bbd3-d3839b80608b
-- title:
--   The L^p estimate for the Cauchy–Riemann operator on a disc
-- statement:
--   Write $z=s+it$ for $z\in\mathbb{C}$, $\varphi_s=\partial\varphi/\partial s$, $\varphi_t=\partial\varphi/\partial t$ and $\bar\partial\varphi=\varphi_s+i\varphi_t$. $\mathbb{C}^n$ carries the Hermitian norm, and $\|\cdot\|_{L^p}$ is the $L^p$ norm on $\mathbb{C}$ with respect to Lebesgue measure. Let $1<p<\infty$ and $R>0$. Then there is a constant $c>1$ such that every smooth $\varphi:\mathbb{C}\to\mathbb{C}^n$ with compact support in the open disc $B_R(0)$ satisfies
--   $$\|\varphi\|_{1,p}\le c\,\|\bar\partial\varphi\|_{L^p},\qquad \|\varphi\|_{1,p}=\big(\|\varphi_s\|_{L^p}^p+\|\varphi_t\|_{L^p}^p+\|\varphi\|_{L^p}^p\big)^{1/p}.$$
--
--   **Formalization Note** `ContDiff ℝ ∞ φ` is $C^\infty$ smoothness over $\mathbb{R}$ (not analyticity). $\varphi_s$ and $\varphi_t$ are `fderiv ℝ φ z 1` and `fderiv ℝ φ z Complex.I`, and $\bar\partial\varphi$ is `dbar φ`. $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`. "Compact support in $B_R(0)$" is `tsupport φ ⊆ ball 0 R`. The norms are `eLpNorm` with exponent `ENNReal.ofReal p`, combined in `ℝ≥0∞`. Abbas–Hofer write $c=c(p,R)$; here $c$ is chosen after $n$ as well, so it may depend on $n$.
-- source:
--   C. Abbas, H. Hofer, Holomorphic Curves and Global Questions in Contact Geometry, Birkhäuser Advanced Texts Basler Lehrbücher, Birkhäuser (2019), https://doi.org/10.1007/978-3-030-11803-7, § 4.2, Theorem 4.2.2, p. 102

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

/-- Abbas–Hofer, *Holomorphic Curves and Global Questions in Contact Geometry*, § 4.2, Theorem 4.2.2
(p. 102): for `1 < p < ∞` and `R > 0` there is `c > 1` such that every smooth `φ : ℂ → ℂⁿ` with
compact support in the open disc `B_R(0)` satisfies `‖φ‖_{1,p} ≤ c ‖∂̄φ‖_{L^p}`, where
`‖φ‖_{1,p} = (‖φ_s‖_p^p + ‖φ_t‖_p^p + ‖φ‖_p^p)^{1/p}` and `z = s + i t`. -/
theorem dbar_lp_estimate (n : ℕ) (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    ∃ c : ℝ, 1 < c ∧ ∀ φ : ℂ → EuclideanSpace ℂ (Fin n), ContDiff ℝ ∞ φ → tsupport φ ⊆ ball 0 R →
      (eLpNorm (fun z => fderiv ℝ φ z 1) (ENNReal.ofReal p) volume ^ p +
          eLpNorm (fun z => fderiv ℝ φ z Complex.I) (ENNReal.ofReal p) volume ^ p +
          eLpNorm φ (ENNReal.ofReal p) volume ^ p) ^ (1 / p)
        ≤ ENNReal.ofReal c * eLpNorm (dbar φ) (ENNReal.ofReal p) volume := by sorry

end DbarRegularity
