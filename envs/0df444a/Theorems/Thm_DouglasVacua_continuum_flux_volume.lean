-- Prove2me | Theorems.Thm_DouglasVacua_continuum_flux_volume
-- name    : DouglasVacua.continuum_flux_volume
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:02:59.517829+00:00
-- url     : https://prove2.me/theorems/49965ade-563d-4317-9348-8d96b0f813e3
-- title:
--   Volume of the continuum flux region $\{c|x|^2\le V\}$
-- statement:
--   Let $J\in\mathbb N$, $c>0$ and $V\ge 0$. The Lebesgue measure of $\{x\in\mathbb R^J : c\sum_{i=1}^J x_i^2\le V\}$ equals
--   $$\frac{\pi^{J/2}}{\Gamma(J/2+1)}\Big(\frac Vc\Big)^{J/2}.$$
--   This is the continuum ("replace the sum with an integral") approximation to the flux vacua count used in (3.13).
-- source:
--   Michael R. Douglas, *The statistics of string/M theory vacua*, JHEP 05 (2003) 046, https://doi.org/10.1088/1126-6708/2003/05/046 (arXiv:hep-th/0303194). Section 3.6, p. 24, eq. (3.13), second line (the sum over $N$ replaced by $\int d^JN$).

import Mathlib
open Real MeasureTheory

namespace DouglasVacua

theorem continuum_flux_volume (J : ℕ) (c V : ℝ) (hc : 0 < c) (hV : 0 ≤ V) :
    volume {x : Fin J → ℝ | c * ∑ i, x i ^ 2 ≤ V} =
      ENNReal.ofReal (π ^ ((J : ℝ) / 2) / Real.Gamma ((J : ℝ) / 2 + 1) *
        (V / c) ^ ((J : ℝ) / 2)) := by sorry

end DouglasVacua
