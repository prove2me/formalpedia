-- Prove2me | Theorems.Thm_CODATA2022_bose_einstein_integral_cube
-- name    : CODATA2022.bose_einstein_integral_cube
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T23:05:04.724619+00:00
-- url     : https://prove2.me/theorems/b57cdc57-364e-4d74-992f-b32c0bf36325
-- title:
--   $\int_0^\infty x^3/(e^x-1)\,dx = \pi^4/15$
-- statement:
--   The Bose-Einstein integral of order four,
--
--   $$\int_0^{\infty}\frac{x^3}{e^x-1}\,\mathrm{d}x \;=\; \Gamma(4)\,\zeta(4) \;=\; 6\cdot\frac{\pi^4}{90} \;=\; \frac{\pi^4}{15},$$
--
--   is the analytic content of the Stefan-Boltzmann law: after the substitution $x = h\nu/kT$ it is the only non-elementary ingredient of the goal theorem.
-- source:
--   Mohr, Newell, Taylor, Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, Rev. Mod. Phys. 97, 025002 (2025), https://doi.org/10.1103/RevModPhys.97.025002, Table XXXII: Stefan-Boltzmann constant (the $\pi^4/15$ factor arising in the derivation of $\sigma$ from Planck's law).

import Mathlib
import Definitions.Def_CODATA2022_si_defining_constants
import Definitions.Def_CODATA2022_radiation_constants
open MeasureTheory

namespace CODATA2022
theorem bose_einstein_integral_cube :
    (∫ x in Set.Ioi (0 : ℝ), x ^ 3 / (Real.exp x - 1)) = Real.pi ^ 4 / 15 := by sorry
end CODATA2022
