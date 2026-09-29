-- Prove2me | Theorems.Thm_AKR2008_mass_cube_uncertainty_minimizer
-- name    : AKR2008.mass_cube_uncertainty_minimizer
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:32:54.686308+00:00
-- url     : https://prove2.me/theorems/6eeb269d-2c42-4f96-b4f4-59cc12500137
-- title:
--   Optimal position uncertainty $\Delta x_{\min}=\sqrt{\tfrac{\hbar}{2m}\tfrac{T_v}{T_a}}$ (Sec. III B)
-- statement:
--   Let $T_a, T_v, \hbar, m > 0$ be as in Sec. III B and consider the lower envelope of the uncertainty of $T^{\mathrm{GW}}_{00}$ as a function of the position uncertainty $\Delta x>0$,
--   $$F(\Delta x) = \sqrt{\bigl(T_a\,\Delta x\bigr)^2 + \Bigl(T_v\,\frac{\hbar}{2m\,\Delta x}\Bigr)^2}.$$
--   Then with
--   $$\Delta x_{\min} = \sqrt{\frac{\hbar}{2m}\,\frac{T_v}{T_a}}$$
--   one has $\Delta x_{\min}>0$, $F(\Delta x_{\min}) \le F(\Delta x)$ for every $\Delta x>0$, and
--   $$F(\Delta x_{\min}) = \sqrt{\frac{\hbar}{m}\,T_v\,T_a}.$$
--
--   This is the paper's statement "The minimum uncertainty is found for $\Delta x_{\min}$ ... and therefore $\Delta T^{\mathrm{GW}}_{00}\ge\sqrt{\tfrac{\hbar}{m}\delta T^{\mathrm{GW}}_{00,v}\delta T^{\mathrm{GW}}_{00,a}}$".
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-8, Sec. III B, formula for $\Delta x_{\min}$

import Mathlib

namespace AKR2008

theorem mass_cube_uncertainty_minimizer
    (Ta Tv ℏ m : ℝ) (hTa : 0 < Ta) (hTv : 0 < Tv) (hℏ : 0 < ℏ) (hm : 0 < m) :
    let F : ℝ → ℝ := fun Δx => Real.sqrt ((Ta * Δx) ^ 2 + (Tv * (ℏ / (2 * m * Δx))) ^ 2)
    let Δxmin : ℝ := Real.sqrt (ℏ / (2 * m) * (Tv / Ta))
    0 < Δxmin ∧ IsMinOn F (Set.Ioi 0) Δxmin ∧ F Δxmin = Real.sqrt (ℏ / m * Tv * Ta) := by
  sorry

end AKR2008
