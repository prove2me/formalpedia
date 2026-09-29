-- Prove2me | Theorems.Thm_CODATA2022_josephson_sq_mul_vonKlitzing
-- name    : CODATA2022.josephson_sq_mul_vonKlitzing
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T23:14:46.155903+00:00
-- url     : https://prove2.me/theorems/b7f41c90-b95c-43cf-8bba-2d1046152c8e
-- title:
--   $K_J^2R_K = 4/h$
-- statement:
--   The Josephson and von Klitzing constants of Table XXXII, $K_J = 2e/h$ and
--   $R_K = h/e^2$, satisfy the identity used in electrical metrology to realize the watt:
--
--   $$K_J^2R_K \;=\; \frac{4e^2}{h^2}\cdot\frac{h}{e^2} \;=\; \frac{4}{h}.$$
--
--   Since $e$ and $h$ are fixed exactly, both constants and their combination are exact.
-- source:
--   Mohr, Newell, Taylor, Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, Rev. Mod. Phys. 97, 025002 (2025), https://doi.org/10.1103/RevModPhys.97.025002, Table XXXII: Josephson constant $K_J = 2e/h$ and von Klitzing constant $R_K = \mu_0c/2\alpha = 2\pi\hbar/e^2$.

import Mathlib
import Definitions.Def_CODATA2022_si_defining_constants
import Definitions.Def_CODATA2022_radiation_constants
open MeasureTheory

namespace CODATA2022
theorem josephson_sq_mul_vonKlitzing :
    josephsonConstant ^ 2 * vonKlitzingConstant = 4 / planckConstant := by sorry
end CODATA2022
