-- Prove2me | Theorems.Thm_AKR2008_osc_gaussian_solves_continuity
-- name    : AKR2008.osc_gaussian_solves_continuity
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T00:03:28.432387+00:00
-- url     : https://prove2.me/theorems/ecc9f32e-08b7-4ef8-86ce-f5c0fd45457f
-- title:
--   Appendix A: the Gaussian $P_{\mathrm{osc}}$ solves the continuity equation
-- statement:
--   Let $\omega,\tau,w$ be real constants and
--   $$P_{\mathrm{osc}}(x,t)=\sqrt{\frac{\tau}{2\pi\cos^2(\omega t)}}\exp\Bigl\{-\frac12\frac{\tau}{\cos^2(\omega t)}\bigl(x-w\cos(\omega t)\bigr)^2\Bigr\},\qquad S_{\mathrm{osc}}(x,t)=-\frac{\omega x^2}{2}\tan(\omega t).$$
--   For every $x$ and every $t$ with $\cos(\omega t)\ne0$,
--   $$\dot P_{\mathrm{osc}} + \frac{\partial}{\partial x}\Bigl(P_{\mathrm{osc}}\,\frac{\partial S_{\mathrm{osc}}}{\partial x}\Bigr) = 0 .$$
--
--   This is the paper's "Gaussian solution" of the oscillator continuity equation, the single-mode analogue of the classical ensemble $P^c[\phi,t]$ of Sec. IV.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-14, Appendix A

import Mathlib
import Definitions.Def_AKR2008_HybridDefs

namespace AKR2008

theorem osc_gaussian_solves_continuity (ω τ w x t : ℝ) (hcos : Real.cos (ω * t) ≠ 0) :
    deriv (fun s => oscP ω τ w x s) t
      + deriv (fun y => oscP ω τ w y t * deriv (fun z => oscS ω z t) y) x = 0 := by sorry

end AKR2008
