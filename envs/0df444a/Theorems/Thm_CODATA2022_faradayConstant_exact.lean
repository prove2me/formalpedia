-- Prove2me | Theorems.Thm_CODATA2022_faradayConstant_exact
-- name    : CODATA2022.faradayConstant_exact
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T23:13:32.990999+00:00
-- url     : https://prove2.me/theorems/6e66df47-fb95-4a81-8cad-808d12ae8e22
-- title:
--   $F = N_Ae = 96\,485.332\,123\,310\,0184$ exactly
-- statement:
--   The Faraday constant $F = N_Ae$ is likewise exactly known:
--
--   $$F \;=\; 6.022\,140\,76\times10^{23}\cdot 1.602\,176\,634\times10^{-19}
--   \;=\; 96\,485.332\,123\,310\,0184\ \mathrm{C\,mol^{-1}},$$
--
--   the value tabulated by CODATA 2022 without uncertainty.
-- source:
--   Mohr, Newell, Taylor, Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, Rev. Mod. Phys. 97, 025002 (2025), https://doi.org/10.1103/RevModPhys.97.025002, Table XXXIII, Physicochemical constants: Faraday constant $N_Ae$ = 96 485.332 123 310 0184 (exact).

import Mathlib
import Definitions.Def_CODATA2022_si_defining_constants
import Definitions.Def_CODATA2022_radiation_constants
open MeasureTheory

namespace CODATA2022
theorem faradayConstant_exact : faradayConstant = 96485.3321233100184 := by sorry
end CODATA2022
