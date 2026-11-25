-- Prove2me | Theorems.Thm_Arxiv2507_15035_adjoint_equation_iff_stationary_field
-- name    : Arxiv2507_15035.adjoint_equation_iff_stationary_field
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T18:34:38.829976+00:00
-- url     : https://prove2.me/theorems/1a6bacff-b203-4f43-8017-adbcd339cd54
-- title:
--   Eq. (7) (as proved): stationarity in the field is the adjoint equation with source $2(u(x_f)-y)$
-- statement:
--   Let $\omega>0$. Let $c$ be a sound speed: measurable, with $c\ge m>0$, and equal to $c_0>0$ outside a bounded region of interest. Let $x_f^{(1)},\dots,x_f^{(M)}\in\mathbb{R}^n$ be the transducer locations and $y\in\mathbb{C}^M$ the measurements. Let $\mathcal L$ be the Lagrangian term of eq. (4) with source $s$. Let $u\in C^2(\mathbb{R}^n;\mathbb{C})$, and let $\lambda$ be locally integrable with $\overline{\lambda}\,(\mathcal S_cu+s)$ integrable. Then the following are equivalent:
--
--   1. for every complex test function $\varphi$, the function $t\mapsto\mathcal L(c,u+t\varphi,\lambda)$, $t\in\mathbb{R}$, has derivative $0$ at $t=0$;
--   2. $\lambda$ solves, in the sense of distributions,
--   $$\mathcal S_c\lambda=\sum_{i=1}^M 2\,\big[u(x_f^{(i)})-y^{(i)}\big]\,\delta(x_f^{(i)}).$$
--
--   This is the second KKT condition, the adjoint equation.
--
--   **Formalization Note** Eq. (7) of the paper has source $\sum_i[u(x_f^{(i)})-y^{(i)}]\delta(x_f^{(i)})$, without the factor $2$. Differentiating the misfit $\|y-u(x_f)\|_2^2$ of eq. (4) produces the factor $2$, so the multiplier of eq. (4) is twice the field $\lambda$ of eq. (7). The statement is the one the derivation establishes, and is titled "as proved". Stationarity is written as the vanishing of every directional derivative along a smooth compactly supported direction.
-- source:
--   Zeng et al., OpenBreastUS: Benchmarking Neural Operators for Wave Imaging Using Breast Ultrasound Computed Tomography, arXiv:2507.15035v1 (2025), claim c022; Section III-B, eqs. (4), (5), (7), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv2507_15035_Basic

open MeasureTheory

namespace Arxiv2507_15035

theorem adjoint_equation_iff_stationary_field {n M : ℕ} (ω : ℝ) (hω : 0 < ω)
    (c : Pt n → ℝ) (ROI : Set (Pt n)) (c0 : ℝ) (hc : IsSoundSpeed c ROI c0)
    (s : Pt n → ℂ) (xf : Fin M → Pt n) (y : Fin M → ℂ)
    (u : Pt n → ℂ) (hu : ContDiff ℝ 2 u) (lam : Pt n → ℂ) (hlam : LocallyIntegrable lam)
    (hint : Integrable (fun x => (starRingEnd ℂ) (lam x) * (helmholtzOp ω c u x + s x))) :
    (∀ φ : Pt n → ℂ, IsTestFn φ →
      HasDerivAt (fun t : ℝ => lagrangianTerm ω c s xf y (fun x => u x + t • φ x) lam) 0 0) ↔
    IsWeakPointSourceSol ω c lam xf (fun i => 2 * (u (xf i) - y i)) := by sorry

end Arxiv2507_15035
