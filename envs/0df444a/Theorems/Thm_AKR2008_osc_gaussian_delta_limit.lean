-- Prove2me | Theorems.Thm_AKR2008_osc_gaussian_delta_limit
-- name    : AKR2008.osc_gaussian_delta_limit
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T00:06:04.742201+00:00
-- url     : https://prove2.me/theorems/243426f1-c8d4-4c86-93fd-35748e53f3a9
-- title:
--   Appendix A: $P_{\mathrm{osc}}\to\delta(x)$ as $\omega t\to\pm\frac\pi2,\pm\frac{3\pi}2,\dots$
-- statement:
--   Let $\omega>0$, $\tau>0$, $w\in\mathbb R$, and let $P_{\mathrm{osc}}$ be the Gaussian ensemble of Appendix A. For every integer $n$ and every bounded continuous function $\varphi:\mathbb R\to\mathbb R$,
--   $$\lim_{t\to t_n,\ t\ne t_n}\int_{\mathbb R}P_{\mathrm{osc}}(x,t)\,\varphi(x)\,dx=\varphi(0),\qquad t_n=\frac{(2n+1)\pi}{2\omega}.$$
--
--   That is, when $\omega t\to\{\pm\frac\pi2,\pm\frac{3\pi}2,\dots\}$, $P_{\mathrm{osc}}(x,t)$ becomes a delta function and the particle is found at $x=0$ with probability one.
--
--   **Formalization Note** "Becomes a delta function" is encoded as weak convergence against bounded continuous test functions, along the punctured neighbourhood of $t_n$ (at $t_n$ itself $\cos(\omega t_n)=0$ and $P_{\mathrm{osc}}$ is not defined in the paper).
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-15, Appendix A

import Mathlib
import Definitions.Def_AKR2008_HybridDefs

namespace AKR2008

theorem osc_gaussian_delta_limit (ω τ w : ℝ) (hω : 0 < ω) (hτ : 0 < τ) (n : ℤ)
    (φ : BoundedContinuousFunction ℝ ℝ) :
    Filter.Tendsto (fun t => ∫ x, oscP ω τ w x t * φ x)
      (nhdsWithin ((2 * n + 1) * Real.pi / (2 * ω)) {((2 * n + 1) * Real.pi / (2 * ω))}ᶜ)
      (nhds (φ 0)) := by sorry

end AKR2008
