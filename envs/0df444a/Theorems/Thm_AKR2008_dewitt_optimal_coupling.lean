-- Prove2me | Theorems.Thm_AKR2008_dewitt_optimal_coupling
-- name    : AKR2008.dewitt_optimal_coupling
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:33:24.2562+00:00
-- url     : https://prove2.me/theorems/954d8f89-bed0-4dc7-a5f4-6bb5634f0d7b
-- title:
--   Optimal coupling in DeWitt's measurement analysis: $\min_g\Delta s=\sqrt{2\,\Delta A\,\Delta D_\Omega s}$ (Eq. (61))
-- statement:
--   In DeWitt's measurement analysis a system observable $s$ is reconstructed from apparatus data as $s = \delta A/g - g\,D_\Omega s$, where $g\neq0$ is the coupling constant. If $A$ and $D_\Omega s$ are known only up to $\Delta A>0$ and $\Delta D_\Omega s>0$, the uncertainty of $s$ is
--   $$\Delta s^2 = \frac{\Delta A^2}{g^2} + g^2\,(\Delta D_\Omega s)^2 .$$
--   Minimized over the coupling constant, this gives
--   $$\min_{g\neq0}\ \Delta s = \sqrt{2\,\Delta A\,\Delta D_\Omega s}. \qquad (61)$$
--   Precisely: $\sqrt{2\,\Delta A\,\Delta D_\Omega s}$ is the least element of the set $\bigl\{\sqrt{\Delta A^2/g^2 + g^2(\Delta D_\Omega s)^2} : g\in\mathbb R,\ g\neq0\bigr\}$.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-12, Sec. V, Eq. (61)

import Mathlib

namespace AKR2008

theorem dewitt_optimal_coupling
    (ΔA ΔD : ℝ) (hA : 0 < ΔA) (hD : 0 < ΔD) :
    IsLeast ((fun g : ℝ => Real.sqrt (ΔA ^ 2 / g ^ 2 + g ^ 2 * ΔD ^ 2)) '' {g : ℝ | g ≠ 0})
      (Real.sqrt (2 * ΔA * ΔD)) := by
  sorry

end AKR2008
