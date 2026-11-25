-- Prove2me | Theorems.Thm_Arxiv2507_15035_lagrangian_deriv_sound_speed
-- name    : Arxiv2507_15035.lagrangian_deriv_sound_speed
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T18:35:09.567157+00:00
-- url     : https://prove2.me/theorems/914bcfed-5fe9-5d98-bbfc-c191d8fafbb5
-- title:
--   Eq. (8) (as proved): the derivative of the Lagrangian in the sound speed is $2\omega^2\,\mathrm{Re}(\lambda^\star u)/c^3$
-- statement:
--   Let $\omega>0$. Let $c$ be a sound speed: measurable, with $c\ge m>0$, and equal to $c_0>0$ outside a bounded region of interest. Let $x_f^{(1)},\dots,x_f^{(M)}\in\mathbb{R}^n$ be the transducer locations and $y\in\mathbb{C}^M$ the measurements. Let $\mathcal L$ be the Lagrangian term of eq. (4) with source $s$. Let $u\in C^2(\mathbb{R}^n;\mathbb{C})$, and let $\lambda$ be locally integrable with $\overline{\lambda}\,(\mathcal S_cu+s)$ integrable. Then, for every real test function $h$, the function $t\mapsto\mathcal L(c+th,u,\lambda)$ is differentiable at $t=0$ with
--   $$\frac{d}{dt}\Big|_{t=0}\mathcal L(c+th,u,\lambda)=\int_{\mathbb{R}^n}\frac{2\omega^2\,\operatorname{Re}\big(\overline{\lambda(x)}\,u(x)\big)}{c(x)^3}\,h(x)\,dx.$$
--   Thus, at fixed $(u,\lambda)$, the partial derivative of the Lagrangian with respect to $c(x)$ is $2\omega^2\operatorname{Re}(\lambda^\star u)/c^3$.
--
--   **Formalization Note** The paper's eq. (8) prints $\partial\mathcal L_k^j/\partial c=(\partial\mathcal S_c/\partial c)\lambda^\star u=-2\omega^2\lambda^\star u/c^3$. Eq. (4) puts a minus sign before the pairing and defines the pairing as a real part. Differentiating it gives $-\operatorname{Re}[\overline\lambda\,(-2\omega^2/c^3)\,u]=+2\omega^2\operatorname{Re}(\overline\lambda u)/c^3$. The statement is that derivative ("as proved"). The partial derivative is written as a directional derivative along compactly supported smooth perturbations $h$ of $c$.
-- source:
--   Zeng et al., OpenBreastUS: Benchmarking Neural Operators for Wave Imaging Using Breast Ultrasound Computed Tomography, arXiv:2507.15035v1 (2025), claim c022; Section III-B, eqs. (4), (5), (8), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv2507_15035_Basic

open MeasureTheory

namespace Arxiv2507_15035

theorem lagrangian_deriv_sound_speed {n M : ℕ} (ω : ℝ) (hω : 0 < ω)
    (c : Pt n → ℝ) (ROI : Set (Pt n)) (c0 : ℝ) (hc : IsSoundSpeed c ROI c0)
    (s : Pt n → ℂ) (xf : Fin M → Pt n) (y : Fin M → ℂ)
    (u : Pt n → ℂ) (hu : ContDiff ℝ 2 u) (lam : Pt n → ℂ) (hlam : LocallyIntegrable lam)
    (hint : Integrable (fun x => (starRingEnd ℂ) (lam x) * (helmholtzOp ω c u x + s x)))
    (h : Pt n → ℝ) (hh : IsTestFn h) :
    HasDerivAt (fun t : ℝ => lagrangianTerm ω (fun x => c x + t * h x) s xf y u lam)
      (∫ x, 2 * ω ^ 2 * ((starRingEnd ℂ) (lam x) * u x).re / c x ^ 3 * h x) 0 := by sorry

end Arxiv2507_15035
