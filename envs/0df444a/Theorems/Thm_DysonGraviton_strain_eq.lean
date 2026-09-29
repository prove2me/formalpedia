-- Prove2me | Theorems.Thm_DysonGraviton_strain_eq
-- name    : DysonGraviton.strain_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T23:23:40.503439+00:00
-- url     : https://prove2.me/theorems/8206c25d-e6c2-4995-bf9f-5bdf86de004f
-- title:
--   Eq. (4) — strain needed to see one graviton
-- statement:
--   Let $c, G, \hbar, \omega, f > 0$. If the energy density of a gravitational wave of strain amplitude $f$ and angular frequency $\omega$ (Eq. (2)) equals the single-graviton energy density bound (Eq. (3)),
--   $$\frac{c^2}{32\pi G}\,\omega^2 f^2 = \frac{\hbar\omega^4}{c^3},$$
--   then
--   $$f = (32\pi)^{1/2}\,\frac{L_p\,\omega}{c},\qquad L_p=\Big(\frac{G\hbar}{c^3}\Big)^{1/2}.$$
-- source:
--   F. Dyson, Is a Graviton Detectable?, Int. J. Mod. Phys. A 28 (2013) 1330041, https://doi.org/10.1142/S0217751X1330041X, p. 4, Eq. (4) (from equating Eqs. (2) and (3))

import Definitions.Def_DysonGraviton_Defs
import Mathlib

open MeasureTheory Filter Topology

namespace DysonGraviton

theorem strain_eq (c G hbar ω f : ℝ) (hc : 0 < c) (hG : 0 < G) (hh : 0 < hbar)
    (hω : 0 < ω) (hf : 0 < f)
    (h : gwEnergyDensity c G ω f = singleGravitonEnergyDensity hbar ω c) :
    f = Real.sqrt (32 * Real.pi) * planckLength G hbar c * ω / c := by
  sorry

end DysonGraviton
