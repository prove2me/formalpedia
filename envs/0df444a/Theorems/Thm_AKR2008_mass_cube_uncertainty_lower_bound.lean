-- Prove2me | Theorems.Thm_AKR2008_mass_cube_uncertainty_lower_bound
-- name    : AKR2008.mass_cube_uncertainty_lower_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T22:32:07.635977+00:00
-- url     : https://prove2.me/theorems/687a832f-5717-4f82-9b65-eea45771455b
-- title:
--   Minimum uncertainty transferred to the gravitational wave: $\Delta T^{\mathrm{GW}}_{00}\ge\sqrt{\tfrac{\hbar}{m}T_vT_a}$ (Sec. III B)
-- statement:
--   Let $T_a = \partial\,\delta T^{\mathrm{GW}}_{00}/\partial a > 0$ and $T_v = \partial\,\delta T^{\mathrm{GW}}_{00}/\partial v > 0$ be the sensitivities of the disturbance of the averaged energy density of the scattered gravitational wave to the edge length $a$ and speed $v$ of the mass cube, let $m>0$ be the mass of a constituent particle and $\hbar>0$. Suppose the edge length is known to within $\Delta a = \Delta x > 0$ and the speed uncertainty obeys the uncertainty principle in the form
--   $$\Delta v \ \ge\ \frac{\hbar}{2m\,\Delta x}.$$
--   Then the resulting classical uncertainty of $T^{\mathrm{GW}}_{00}$ satisfies
--   $$\Delta T^{\mathrm{GW}}_{00} = \sqrt{(T_a\,\Delta x)^2 + (T_v\,\Delta v)^2}\ \ge\ \sqrt{\frac{\hbar}{m}\,T_v\,T_a}.$$
--
--   This is the paper's conclusion that "a coupling between a weak gravitational wave and a test body obeying the uncertainty principle ... unavoidably transfers a minimum amount of uncertainty to the classical system".
--
--   **Formalization Note** The paper's approximate relations $\Delta a\approx\Delta x$ and $\Delta p\gtrsim\hbar/\Delta x$ are encoded as $\Delta a=\Delta x$ and the hypothesis on $\Delta v$ displayed above (with the factor $2$ used in the paper's displayed formula). Positivity of $T_a$ and $T_v$ is assumed, as the paper's square roots presuppose.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-8, Sec. III B, uncertainty estimate following Eq. (35)

import Mathlib

namespace AKR2008

theorem mass_cube_uncertainty_lower_bound
    (Ta Tv ℏ m : ℝ) (hTa : 0 < Ta) (hTv : 0 < Tv) (hℏ : 0 < ℏ) (hm : 0 < m)
    (Δx Δv : ℝ) (hΔx : 0 < Δx) (hΔv : ℏ / (2 * m * Δx) ≤ Δv) :
    Real.sqrt (ℏ / m * Tv * Ta) ≤ Real.sqrt ((Ta * Δx) ^ 2 + (Tv * Δv) ^ 2) := by
  sorry

end AKR2008
