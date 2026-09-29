-- Prove2me | Theorems.Thm_CODATA2022_molarGasConstant_exact
-- name    : CODATA2022.molarGasConstant_exact
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T23:13:09.151319+00:00
-- url     : https://prove2.me/theorems/7775171a-73ca-4835-904d-854f14e24995
-- title:
--   $R = N_Ak = 8.314\,462\,618\,153\,24$ exactly
-- statement:
--   Because both $N_A$ and $k$ have exact fixed values, the molar gas constant
--   $R = N_Ak$ is an exact rational number, and the product terminates:
--
--   $$R \;=\; 6.022\,140\,76\times10^{23}\cdot 1.380\,649\times10^{-23}
--   \;=\; 8.314\,462\,618\,153\,24\ \mathrm{J\,mol^{-1}K^{-1}},$$
--
--   as tabulated by CODATA 2022 with no uncertainty attached.
-- source:
--   Mohr, Newell, Taylor, Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, Rev. Mod. Phys. 97, 025002 (2025), https://doi.org/10.1103/RevModPhys.97.025002, Table XXXIII, Physicochemical constants: molar gas constant $N_Ak$ = 8.314 462 618 153 24 (exact).

import Mathlib
import Definitions.Def_CODATA2022_si_defining_constants
import Definitions.Def_CODATA2022_radiation_constants
open MeasureTheory

namespace CODATA2022
theorem molarGasConstant_exact : molarGasConstant = 8.31446261815324 := by sorry
end CODATA2022
