-- Prove2me | Theorems.Thm_Arxiv2507_15035_adjoint_state_gradient
-- name    : Arxiv2507_15035.adjoint_state_gradient
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T18:35:54.563978+00:00
-- url     : https://prove2.me/theorems/46abd67d-e659-467d-922b-f7ba22d6aeca
-- title:
--   Eqs. (6)-(8) (as proved): the KKT multiplier is twice the adjoint field and the gradient is $4\omega^2\,\mathrm{Re}(\lambda^\star u)/c^3$
-- statement:
--   Let $\omega>0$. Let $c$ be a sound speed: measurable, with $c\ge m>0$, and equal to $c_0>0$ outside a bounded region of interest. Let $x_f^{(1)},\dots,x_f^{(M)}\in\mathbb{R}^n$ be the transducer locations and $y\in\mathbb{C}^M$ the measurements. Let $\mathcal L$ be the Lagrangian term of eq. (4) with source $s$. Let $u\in C^2(\mathbb{R}^n;\mathbb{C})$ solve the forward equation (6), $\mathcal S_cu=-s$ almost everywhere. Let $\lambda$ solve the adjoint equation (7) as printed, in the sense of distributions:
--   $$\mathcal S_c\lambda=\sum_{i=1}^M\big[u(x_f^{(i)})-y^{(i)}\big]\,\delta(x_f^{(i)}).$$
--   Then, with the multiplier $2\lambda$:
--
--   1. $\mathcal L(c,u,\cdot)$ is stationary at $2\lambda$: $\frac{d}{dt}\big|_{t=0}\mathcal L(c,u,2\lambda+t\varphi)=0$ for every complex test function $\varphi$;
--   2. $\mathcal L(c,\cdot,2\lambda)$ is stationary at $u$: $\frac{d}{dt}\big|_{t=0}\mathcal L(c,u+t\varphi,2\lambda)=0$ for every complex test function $\varphi$;
--   3. for every real test function $h$,
--   $$\frac{d}{dt}\Big|_{t=0}\mathcal L(c+th,u,2\lambda)=\int_{\mathbb{R}^n}\frac{4\omega^2\,\operatorname{Re}\big(\overline{\lambda(x)}\,u(x)\big)}{c(x)^3}\,h(x)\,dx.$$
--
--   So a forward solve and an adjoint solve give the gradient of the Lagrangian with respect to the sound speed, with density $4\omega^2\operatorname{Re}(\lambda^\star u)/c^3$. This is the adjoint-state computation that the paper's neural surrogates accelerate.
--
--   **Formalization Note** The paper's eq. (8) prints the gradient as $-2\omega^2\lambda^\star u/c^3$, with $\lambda$ the field of eq. (7). The derivation from eqs. (4), (5) and (7) gives $+4\omega^2\operatorname{Re}(\lambda^\star u)/c^3$. The printed formula differs by a factor $-2$ and omits the real part. The statement is the formula the derivation establishes ("as proved"). Stationarity and partial derivatives are written as directional derivatives along smooth compactly supported directions.
-- source:
--   Zeng et al., OpenBreastUS: Benchmarking Neural Operators for Wave Imaging Using Breast Ultrasound Computed Tomography, arXiv:2507.15035v1 (2025), claim c022; Section III-B, eqs. (4)-(8), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv2507_15035_Basic

open MeasureTheory

namespace Arxiv2507_15035

theorem adjoint_state_gradient {n M : ℕ} (ω : ℝ) (hω : 0 < ω)
    (c : Pt n → ℝ) (ROI : Set (Pt n)) (c0 : ℝ) (hc : IsSoundSpeed c ROI c0)
    (s : Pt n → ℂ) (xf : Fin M → Pt n) (y : Fin M → ℂ)
    (u : Pt n → ℂ) (hu : ContDiff ℝ 2 u) (hfwd : ∀ᵐ x, helmholtzOp ω c u x = -s x)
    (lam : Pt n → ℂ) (hadj : IsWeakPointSourceSol ω c lam xf (fun i => u (xf i) - y i)) :
    (∀ φ : Pt n → ℂ, IsTestFn φ →
      HasDerivAt (fun t : ℝ => lagrangianTerm ω c s xf y u (fun x => 2 * lam x + t • φ x)) 0 0) ∧
    (∀ φ : Pt n → ℂ, IsTestFn φ →
      HasDerivAt (fun t : ℝ =>
        lagrangianTerm ω c s xf y (fun x => u x + t • φ x) (fun x => 2 * lam x)) 0 0) ∧
    (∀ h : Pt n → ℝ, IsTestFn h →
      HasDerivAt (fun t : ℝ =>
        lagrangianTerm ω (fun x => c x + t * h x) s xf y u (fun x => 2 * lam x))
        (∫ x, 4 * ω ^ 2 * ((starRingEnd ℂ) (lam x) * u x).re / c x ^ 3 * h x) 0) := by sorry

end Arxiv2507_15035
