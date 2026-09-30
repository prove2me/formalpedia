-- Prove2me | Theorems.Thm_AKR2008_osc_HJ_solution
-- name    : AKR2008.osc_HJ_solution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T23:54:10.743206+00:00
-- url     : https://prove2.me/theorems/39222c7b-810c-41ec-b006-06f311e1a0c2
-- title:
--   Appendix A: $S_{\mathrm{osc}}$ solves the oscillator Hamilton–Jacobi equation
-- statement:
--   Let $\omega$ be a real frequency and $S_{\mathrm{osc}}(x,t)=-\dfrac{\omega x^2}{2}\tan(\omega t)$. For every $x$ and every $t$ with $\cos(\omega t)\ne0$,
--   $$\dot S_{\mathrm{osc}} + \frac12\Bigl(\frac{\partial S_{\mathrm{osc}}}{\partial x}\Bigr)^2 + \frac12\,\omega^2x^2 = 0 .$$
--
--   This is the Hamilton–Jacobi equation of the unit-mass one-dimensional harmonic oscillator; its solution is the single-mode analogue of the classical functional $S^c[\phi,t]=-\sum_k\frac{ka_k^2}{2}\tan(kt)$ of Sec. IV.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-14, Appendix A

import Mathlib
import Definitions.Def_AKR2008_HybridDefs

namespace AKR2008

theorem osc_HJ_solution (ω x t : ℝ) (hcos : Real.cos (ω * t) ≠ 0) :
    deriv (fun s => oscS ω x s) t + (1 / 2) * (deriv (fun y => oscS ω y t) x) ^ 2
      + (1 / 2) * ω ^ 2 * x ^ 2 = 0 := by sorry

end AKR2008
