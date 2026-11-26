-- Prove2me | Theorems.Thm_Arxiv2507_15035_forward_equation_iff_stationary_multiplier
-- name    : Arxiv2507_15035.forward_equation_iff_stationary_multiplier
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T18:34:03.107732+00:00
-- url     : https://prove2.me/theorems/31bd5856-e7dd-458a-bb7c-482ced3c5472
-- title:
--   Eq. (6): stationarity in the multiplier is the forward Helmholtz equation
-- statement:
--   Let $\omega>0$. Let $c$ be a sound speed: measurable, with $c\ge m>0$, and equal to $c_0>0$ outside a bounded region of interest. Let $x_f^{(1)},\dots,x_f^{(M)}\in\mathbb{R}^n$ be the transducer locations and $y\in\mathbb{C}^M$ the measurements. Let $\mathcal L$ be the Lagrangian term of eq. (4) with source $s$. Let $s$ be locally integrable, let $u\in C^2(\mathbb{R}^n;\mathbb{C})$, and let $\lambda:\mathbb{R}^n\to\mathbb{C}$ be such that $\overline{\lambda}\,(\mathcal S_cu+s)$ is integrable. Then the following are equivalent:
--
--   1. for every complex test function $\varphi$, the function $t\mapsto\mathcal L(c,u,\lambda+t\varphi)$, $t\in\mathbb{R}$, has derivative $0$ at $t=0$;
--   2. $u$ solves the forward Helmholtz equation (6) almost everywhere:
--   $$\mathcal S_cu(x)=-s(x)\quad\text{for a.e. }x\in\mathbb{R}^n.$$
--
--   This is the first KKT condition of the Lagrangian formulation of full-waveform inversion: varying the multiplier recovers the constraint.
--
--   **Formalization Note** The paper's condition $\partial\mathcal L_k^j/\partial\lambda_k^j(x)=0$ is written as the vanishing of every directional derivative of $\mathcal L$ along a smooth compactly supported direction. The source $s$ is a locally integrable function. A point source (Dirac mass), which the paper also calls $s_k$, is outside this function class.
-- source:
--   Zeng et al., OpenBreastUS: Benchmarking Neural Operators for Wave Imaging Using Breast Ultrasound Computed Tomography, arXiv:2507.15035v1 (2025), claim c022; Section III-B, eqs. (4)-(6), PDF p. 4 (forward model eqs. (1), (3), PDF p. 3)

import Mathlib
import Definitions.Def_Arxiv2507_15035_Basic

open MeasureTheory

namespace Arxiv2507_15035

theorem forward_equation_iff_stationary_multiplier {n M : ℕ} (ω : ℝ) (hω : 0 < ω)
    (c : Pt n → ℝ) (ROI : Set (Pt n)) (c0 : ℝ) (hc : IsSoundSpeed c ROI c0)
    (s : Pt n → ℂ) (hs : LocallyIntegrable s) (xf : Fin M → Pt n) (y : Fin M → ℂ)
    (u : Pt n → ℂ) (hu : ContDiff ℝ 2 u) (lam : Pt n → ℂ)
    (hint : Integrable (fun x => (starRingEnd ℂ) (lam x) * (helmholtzOp ω c u x + s x))) :
    (∀ φ : Pt n → ℂ, IsTestFn φ →
      HasDerivAt (fun t : ℝ => lagrangianTerm ω c s xf y u (fun x => lam x + t • φ x)) 0 0) ↔
    ∀ᵐ x, helmholtzOp ω c u x = -s x := by sorry

end Arxiv2507_15035
