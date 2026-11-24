-- Prove2me | Theorems.Thm_Arxiv1310_4241_pec_mie_spectral_densities
-- name    : Arxiv1310_4241.pec_mie_spectral_densities
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:23:50.547287+00:00
-- url     : https://prove2.me/theorems/d8159ba2-ee4a-4650-881f-63fb639cb1fa
-- title:
--   Eq. (31) (as derived): the spectral densities $\widehat\sigma,\widehat\tau$ from $\mathbf n\times\mathbf E^{\rm tot}=0$
-- statement:
--   Let $k=\omega\sqrt{\varepsilon\mu}$ with $\operatorname{Re}k>0$, $\operatorname{Im}k\ge0$, let $(\xi,\eta)\ne(0,0)$ with $\beta=\sqrt{\xi^2+\eta^2-k^2}\ne0$, and let $\widehat E^{\rm in}_x,\widehat E^{\rm in}_y\in\mathbb C$. Then $(\widehat\sigma,\widehat\tau)$ solves the system that $\mathbf n\times\mathbf E^{\rm tot}=0$ on $z=0$ gives with the boundary values of eq. (29) as derived (statement mie_tangential_boundary_values),
--
--   $$\widehat g_k(\xi,\eta,0)\big(-i\xi\beta\widehat\sigma-\omega\mu\eta\widehat\tau\big)=-\widehat E^{\rm in}_x,\qquad \widehat g_k(\xi,\eta,0)\big(-i\eta\beta\widehat\sigma+\omega\mu\xi\widehat\tau\big)=-\widehat E^{\rm in}_y,$$
--
--   if and only if
--
--   $$\widehat\sigma=-\frac{8\pi^2i}{\xi^2+\eta^2}\big(\xi\widehat E^{\rm in}_x+\eta\widehat E^{\rm in}_y\big),\qquad \widehat\tau=\frac{8\pi^2\beta}{\omega\mu(\xi^2+\eta^2)}\big(\eta\widehat E^{\rm in}_x-\xi\widehat E^{\rm in}_y\big).$$
--
--   **Formalization Note** This is the system (30) and its solution (31) as they follow from $\mathbf n\times\mathbf E^{\rm tot}=0$ and the derived (29). The printed (30) inherits the sign error of (29) in the $\widehat\sigma$-coefficients ($+i\xi\beta$, $+i\eta\beta$), so the printed $\widehat\sigma$ in (31) has the wrong overall sign. The printed $\widehat\tau$ has $\eta\widehat E^{\rm in}_y-\xi\widehat E^{\rm in}_x$, with $E_x$ and $E_y$ interchanged; the paper's next sentence uses $\eta\widehat E^{\rm in}_x-\xi\widehat E^{\rm in}_y$, which is the correct one. The modes with $\xi^2+\eta^2=k^2$, where $\widehat g_k$ is infinite, are excluded.
-- source:
--   M. O'Neil, A generalized Debye source approach to electromagnetic scattering in layered media, arXiv:1310.4241v1 (2013), claim c008; Section IV, eqs. (30) and (31), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology

namespace Arxiv1310_4241

theorem pec_mie_spectral_densities (ω : ℝ) (ε μ k : ℂ) (hkdef : k = wavenumber ω ε μ)
    (hk : IsCausalWavenumber k) (ξ η : ℝ) (hξη : (ξ, η) ≠ (0, 0))
    (hβ : sommerfeldRoot k ξ η ≠ 0) (Ex Ey σ τ : ℂ) :
    (ghat k ξ η 0 * (-(Complex.I * ξ * sommerfeldRoot k ξ η * σ) - ω * μ * η * τ) = -Ex ∧
      ghat k ξ η 0 * (-(Complex.I * η * sommerfeldRoot k ξ η * σ) + ω * μ * ξ * τ) = -Ey) ↔
    (σ = -(8 * Real.pi ^ 2 * Complex.I / ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2)) * (ξ * Ex + η * Ey) ∧
      τ = 8 * Real.pi ^ 2 * sommerfeldRoot k ξ η / (ω * μ * ((ξ : ℂ) ^ 2 + (η : ℂ) ^ 2)) *
        (η * Ex - ξ * Ey)) := by sorry

end Arxiv1310_4241
